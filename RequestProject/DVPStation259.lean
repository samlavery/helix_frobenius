import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 259` (rung-262.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT259 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((259 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))

theorem st259_c1 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((991079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167091/5000000) (δ := 201/1000000000) (ψ := -133673/1000000) 259 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t1 : ((991029/1000000 : ℚ) : ℝ) ≤ stT259 1 := by
  have hc : ((991029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((991029/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((991029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c2 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-16641/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6383973/10000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 29
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t2 : ((-14709589207/25000000000 : ℚ) : ℝ) ≤ stT259 2 := by
  have hc : ((-8321/10000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14709589207/25000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-8321/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c3 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-176189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4827267/10000000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 45
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t3 : ((-508686028821/2500000000000 : ℚ) : ℝ) ≤ stT259 3 := by
  have hc : ((-88107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508686028821/2500000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-88107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c4 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((100839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 651467/2500000) (δ := 13011/1000000000) (ψ := -133673/1000000) 259 57
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t4 : ((100829/400000 : ℚ) : ℝ) ≤ stT259 4 := by
  have hc : ((100829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100829/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((100829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c5 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-657183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5719679/10000000) (δ := 1641/125000000) (ψ := -133673/1000000) 259 66
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t5 : ((-367404419961/1250000000000 : ℚ) : ℝ) ≤ stT259 5 := by
  have hc : ((-657233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367404419961/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-657233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c6 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((727351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378171/2000000) (δ := 13133/1000000000) (ψ := -133673/1000000) 259 74
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t6 : ((1484596620541/5000000000000 : ℚ) : ℝ) ≤ stT259 6 := by
  have hc : ((727301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1484596620541/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((727301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c7 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((50523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3673943/10000000) (δ := 13027/1000000000) (ψ := -133673/1000000) 259 80
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t7 : ((23858057839/625000000000 : ℚ) : ℝ) ≤ stT259 7 := by
  have hc : ((25249/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23858057839/625000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((25249/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c8 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-37019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -822451/2000000) (δ := 1623/125000000) (ψ := -133673/1000000) 259 86
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t8 : ((-16371290187/625000000000 : ℚ) : ℝ) ≤ stT259 8 := by
  have hc : ((-9261/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16371290187/625000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-9261/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c9 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-832849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6387579/10000000) (δ := 1631/125000000) (ψ := -133673/1000000) 259 91
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t9 : ((-1388165277633/5000000000000 : ℚ) : ℝ) ≤ stT259 9 := by
  have hc : ((-832899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1388165277633/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-832899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c10 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((921293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249627/2500000) (δ := 1623/125000000) (ψ := -133673/1000000) 259 95
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t10 : ((2913225550311/10000000000000 : ℚ) : ℝ) ≤ stT259 10 := by
  have hc : ((921243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2913225550311/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((921243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c11 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((331191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2117007/10000000) (δ := 13091/1000000000) (ψ := -133673/1000000) 259 99
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t11 : ((499251455879/2500000000000 : ℚ) : ℝ) ≤ stT259 11 := by
  have hc : ((165583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499251455879/2500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((165583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c12 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-119343/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1419797/2000000) (δ := 12969/1000000000) (ψ := -133673/1000000) 259 102
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t12 : ((-43066460767/156250000000 : ℚ) : ℝ) ≤ stT259 12 := by
  have hc : ((-477397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43066460767/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-477397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c13 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((2177/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195261/500000) (δ := 163/12500000) (ψ := -133673/1000000) 259 106
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t13 : ((24012963/10000000000 : ℚ) : ℝ) ≤ stT259 13 := by
  have hc : ((4329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24012963/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((4329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c14 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((345831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -152209/500000) (δ := 13119/1000000000) (ψ := -133673/1000000) 259 109
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t14 : ((231034612493/2500000000000 : ℚ) : ℝ) ≤ stT259 14 := by
  have hc : ((345781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231034612493/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((345781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c15 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-586937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5495167/10000000) (δ := 13097/1000000000) (ψ := -133673/1000000) 259 112
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t15 : ((-1515593977143/10000000000000 : ℚ) : ℝ) ≤ stT259 15 := by
  have hc : ((-586987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1515593977143/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-586987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c16 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-185571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2438793/5000000) (δ := 41/3125000) (ψ := -133673/1000000) 259 114
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t16 : ((-115997546399/1250000000000 : ℚ) : ℝ) ≤ stT259 16 := by
  have hc : ((-46399/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115997546399/1250000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-46399/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c17 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((73077/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -747969/2500000) (δ := 13061/1000000000) (ψ := -133673/1000000) 259 117
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t17 : ((44303371713/500000000000 : ℚ) : ℝ) ≤ stT259 17 := by
  have hc : ((73067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44303371713/500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((73067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c18 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((3159/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1301131/5000000) (δ := 51/3906250) (ψ := -133673/1000000) 259 119
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t18 : ((59560767429/500000000000 : ℚ) : ℝ) ≤ stT259 18 := by
  have hc : ((50539/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59560767429/500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((50539/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c19 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-787747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6194847/10000000) (δ := 13033/1000000000) (ψ := -133673/1000000) 259 121
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t19 : ((-903665394963/5000000000000 : ℚ) : ℝ) ≤ stT259 19 := by
  have hc : ((-787797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-903665394963/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-787797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c20 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-998491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7716631/10000000) (δ := 13011/1000000000) (ψ := -133673/1000000) 259 124
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t20 : ((-558201394197/2500000000000 : ℚ) : ℝ) ≤ stT259 20 := by
  have hc : ((-998541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558201394197/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-998541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c21 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-992169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7540903/10000000) (δ := 12997/1000000000) (ψ := -133673/1000000) 259 126
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t21 : ((-2165199465201/10000000000000 : ℚ) : ℝ) ≤ stT259 21 := by
  have hc : ((-992219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2165199465201/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-992219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c22 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-923971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3436417/5000000) (δ := 13013/1000000000) (ψ := -133673/1000000) 259 127
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t22 : ((-246252520521/1250000000000 : ℚ) : ℝ) ≤ stT259 22 := by
  have hc : ((-924021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246252520521/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-924021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c23 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-62329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529931/1250000) (δ := 3257/250000000) (ψ := -133673/1000000) 259 129
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t23 : ((-13001713133/500000000000 : ℚ) : ℝ) ≤ stT259 23 := by
  have hc : ((-31177/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13001713133/500000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-31177/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c24 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((494209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 190431/5000000) (δ := 13061/1000000000) (ψ := -133673/1000000) 259 131
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t24 : ((126093580293/625000000000 : ℚ) : ℝ) ≤ stT259 24 := by
  have hc : ((61773/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126093580293/625000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((61773/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c25 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-267051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4602819/10000000) (δ := 51/3906250) (ψ := -133673/1000000) 259 133
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t25 : ((-534202267101/10000000000000 : ℚ) : ℝ) ≤ stT259 25 := by
  have hc : ((-267101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534202267101/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-267101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c26 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-446681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5084621/10000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 134
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t26 : ((-438055930711/5000000000000 : ℚ) : ℝ) ≤ stT259 26 := by
  have hc : ((-446731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438055930711/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-446731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c27 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((18159/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -947231/5000000) (δ := 21/1600000) (ψ := -133673/1000000) 259 136
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t27 : ((279556719/2000000000 : ℚ) : ℝ) ≤ stT259 27 := by
  have hc : ((72631/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279556719/2000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((72631/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c28 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-722539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5945661/10000000) (δ := 2597/200000000) (ψ := -133673/1000000) 259 137
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t28 : ((-1365565311747/10000000000000 : ℚ) : ℝ) ≤ stT259 28 := by
  have hc : ((-722589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1365565311747/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-722589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c29 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((227039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2748649/10000000) (δ := 3251/250000000) (ψ := -133673/1000000) 259 139
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t29 : ((210777164171/2500000000000 : ℚ) : ℝ) ≤ stT259 29 := by
  have hc : ((113507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210777164171/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((113507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c30 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((43023/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3494609/10000000) (δ := 3249/250000000) (ψ := -133673/1000000) 259 140
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t30 : ((157052066561/5000000000000 : ℚ) : ℝ) ≤ stT259 30 := by
  have hc : ((86021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157052066561/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((86021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c31 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-89353/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6689857/10000000) (δ := 13021/1000000000) (ψ := -133673/1000000) 259 142
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t31 : ((-40122948333/250000000000 : ℚ) : ℝ) ≤ stT259 31 := by
  have hc : ((-44679/50000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40122948333/250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-44679/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c32 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((92627/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1840537/10000000) (δ := 3257/250000000) (ψ := -133673/1000000) 259 143
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t32 : ((327463625489/2500000000000 : ℚ) : ℝ) ≤ stT259 32 := by
  have hc : ((370483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327463625489/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((370483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c33 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((290661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2376111/10000000) (δ := 2627/200000000) (ψ := -133673/1000000) 259 144
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t33 : ((15810380423/156250000000 : ℚ) : ℝ) ≤ stT259 33 := by
  have hc : ((72659/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15810380423/156250000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((72659/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c34 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-184211/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1199593/2000000) (δ := 13043/1000000000) (ψ := -133673/1000000) 259 145
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t34 : ((-315940723371/2500000000000 : ℚ) : ℝ) ≤ stT259 34 := by
  have hc : ((-368447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315940723371/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-368447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c35 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-885991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1662139/2500000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 147
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t35 : ((-1497683076669/10000000000000 : ℚ) : ℝ) ≤ stT259 35 := by
  have hc : ((-886041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1497683076669/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-886041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c36 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-18869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4115861/10000000) (δ := 3241/250000000) (ψ := -133673/1000000) 259 148
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t36 : ((-62938345921/5000000000000 : ℚ) : ℝ) ≤ stT259 36 := by
  have hc : ((-37763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62938345921/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-37763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c37 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((672519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -520743/2500000) (δ := 1629/125000000) (ψ := -133673/1000000) 259 149
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t37 : ((1105531638841/10000000000000 : ℚ) : ℝ) ≤ stT259 37 := by
  have hc : ((672469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1105531638841/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((672469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c38 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((489087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -130819/2500000) (δ := 21/1600000) (ψ := -133673/1000000) 259 150
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t38 : ((198340805817/1250000000000 : ℚ) : ℝ) ≤ stT259 38 := by
  have hc : ((244531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198340805817/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((244531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c39 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((972477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587897/10000000) (δ := 13117/1000000000) (ψ := -133673/1000000) 259 151
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t39 : ((1557128878987/10000000000000 : ℚ) : ℝ) ≤ stT259 39 := by
  have hc : ((972427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1557128878987/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((972427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c40 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((436547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127321/1000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 152
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t40 : ((172550380509/1250000000000 : ℚ) : ℝ) ≤ stT259 40 := by
  have hc : ((218261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172550380509/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((218261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c41 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((101627/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310741/2000000) (δ := 13/1000000) (ψ := -133673/1000000) 259 153
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t41 : ((634819540971/5000000000000 : ℚ) : ℝ) ≤ stT259 41 := by
  have hc : ((406483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634819540971/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((406483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c42 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((167339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724469/5000000) (δ := 13107/1000000000) (ψ := -133673/1000000) 259 154
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t42 : ((258194168857/2000000000000 : ℚ) : ℝ) ≤ stT259 42 := by
  have hc : ((167329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258194168857/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((167329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c43 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((924609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976973/10000000) (δ := 12989/1000000000) (ψ := -133673/1000000) 259 155
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t43 : ((281987721323/2000000000000 : ℚ) : ℝ) ≤ stT259 43 := by
  have hc : ((924559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281987721323/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((924559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c44 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((499043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 154711/10000000) (δ := 12981/1000000000) (ψ := -133673/1000000) 259 156
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t44 : ((94037197501/625000000000 : ℚ) : ℝ) ≤ stT259 44 := by
  have hc : ((249509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94037197501/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((249509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c45 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((920731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501057/5000000) (δ := 13029/1000000000) (ψ := -133673/1000000) 259 157
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t45 : ((1372469294191/10000000000000 : ℚ) : ℝ) ≤ stT259 45 := by
  have hc : ((920681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1372469294191/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((920681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c46 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((547439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123937/500000) (δ := 13067/1000000000) (ψ := -133673/1000000) 259 158
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t46 : ((807080741991/10000000000000 : ℚ) : ℝ) ≤ stT259 46 := by
  have hc : ((547389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((807080741991/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((547389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c47 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-26671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2130687/5000000) (δ := 653/50000000) (ψ := -133673/1000000) 259 159
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t47 : ((-778364813/40000000000 : ℚ) : ℝ) ≤ stT259 47 := by
  have hc : ((-26681/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778364813/40000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-26681/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c48 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-41077/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316863/500000) (δ := 263/20000000) (ψ := -133673/1000000) 259 160
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t48 : ((-7411645549/62500000000 : ℚ) : ℝ) ≤ stT259 48 := by
  have hc : ((-82159/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7411645549/62500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-82159/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c49 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-23601/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 876709/1250000) (δ := 263/20000000) (ψ := -133673/1000000) 259 160
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t49 : ((-33717513487/250000000000 : ℚ) : ℝ) ≤ stT259 49 := by
  have hc : ((-94409/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33717513487/250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-94409/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c50 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-7319/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4387021/10000000) (δ := 6523/500000000) (ψ := -133673/1000000) 259 161
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t50 : ((-5176730347/200000000000 : ℚ) : ℝ) ≤ stT259 50 := by
  have hc : ((-7321/40000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5176730347/200000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-7321/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c51 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((165011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1501241/10000000) (δ := 6569/500000000) (ψ := -133673/1000000) 259 162
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t51 : ((5776190007/50000000000 : ℚ) : ℝ) ≤ stT259 51 := by
  have hc : ((165001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5776190007/50000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((165001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c52 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((794021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -816751/5000000) (δ := 3243/250000000) (ψ := -133673/1000000) 259 163
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t52 : ((4404157137/40000000000 : ℚ) : ℝ) ≤ stT259 52 := by
  have hc : ((793971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4404157137/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((793971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c53 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-209483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1251939/2500000) (δ := 407/31250000) (ψ := -133673/1000000) 259 164
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t53 : ((-35972680731/625000000000 : ℚ) : ℝ) ≤ stT259 53 := by
  have hc : ((-52377/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35972680731/625000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-52377/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c54 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-477157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7095379/10000000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 164
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t54 : ((-81170328337/625000000000 : ℚ) : ℝ) ≤ stT259 54 := by
  have hc : ((-238591/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81170328337/625000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-238591/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c55 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((260377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1634229/5000000) (δ := 6493/500000000) (ψ := -133673/1000000) 259 165
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t55 : ((351024666473/10000000000000 : ℚ) : ℝ) ≤ stT259 55 := by
  have hc : ((260327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351024666473/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((260327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c56 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((190527/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772527/10000000) (δ := 1311/100000000) (ψ := -133673/1000000) 259 166
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t56 : ((127294505101/1000000000000 : ℚ) : ℝ) ≤ stT259 56 := by
  have hc : ((190517/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127294505101/1000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((190517/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c57 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-423407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5019999/10000000) (δ := 13003/1000000000) (ψ := -133673/1000000) 259 167
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t57 : ((-560882770581/10000000000000 : ℚ) : ℝ) ≤ stT259 57 := by
  have hc : ((-423457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-560882770581/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-423457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c58 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-79903/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 780149/1250000) (δ := 131/10000000) (ψ := -133673/1000000) 259 167
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t58 : ((-5246219901/50000000000 : ℚ) : ℝ) ≤ stT259 58 := by
  have hc : ((-19977/25000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5246219901/50000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-19977/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c59 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((801653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400463/2500000) (δ := 2619/200000000) (ψ := -133673/1000000) 259 168
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t59 : ((1043598128067/10000000000000 : ℚ) : ℝ) ≤ stT259 59 := by
  have hc : ((801603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1043598128067/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((801603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c60 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((69423/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1611757/5000000) (δ := 409/31250000) (ψ := -133673/1000000) 259 169
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t60 : ((89608539037/2500000000000 : ℚ) : ℝ) ≤ stT259 60 := by
  have hc : ((138821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89608539037/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((138821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c61 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-197757/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 934901/1250000) (δ := 3247/250000000) (ψ := -133673/1000000) 259 169
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t61 : ((-253214736023/2000000000000 : ℚ) : ℝ) ≤ stT259 61 := by
  have hc : ((-197767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253214736023/2000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-197767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c62 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((302923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2299919/10000000) (δ := 6561/500000000) (ψ := -133673/1000000) 259 170
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t62 : ((192340381449/2500000000000 : ℚ) : ℝ) ≤ stT259 62 := by
  have hc : ((151449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192340381449/2500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((151449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c63 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((344477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1523893/5000000) (δ := 6537/500000000) (ψ := -133673/1000000) 259 171
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t63 : ((433937033187/10000000000000 : ℚ) : ℝ) ≤ stT259 63 := by
  have hc : ((344427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433937033187/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((344427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c64 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-960529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7149239/10000000) (δ := 13129/1000000000) (ψ := -133673/1000000) 259 171
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t64 : ((-1200724710579/10000000000000 : ℚ) : ℝ) ≤ stT259 64 := by
  have hc : ((-960579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1200724710579/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-960579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c65 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((207443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 296049/2000000) (δ := 3259/250000000) (ψ := -133673/1000000) 259 172
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t65 : ((514571596767/5000000000000 : ℚ) : ℝ) ≤ stT259 65 := by
  have hc : ((414861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514571596767/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((414861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c66 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-165247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1085503/2500000) (δ := 3261/250000000) (ψ := -133673/1000000) 259 173
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t66 : ((-40693311351/2000000000000 : ℚ) : ℝ) ≤ stT259 66 := by
  have hc : ((-165297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40693311351/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-165297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c67 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-110809/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1348757/2500000) (δ := 12959/1000000000) (ψ := -133673/1000000) 259 173
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t67 : ((-27077403641/400000000000 : ℚ) : ℝ) ≤ stT259 67 := by
  have hc : ((-110819/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27077403641/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-110819/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c68 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((239699/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360079/5000000) (δ := 1619/125000000) (ψ := -133673/1000000) 259 174
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t68 : ((290662545447/2500000000000 : ℚ) : ℝ) ≤ stT259 68 := by
  have hc : ((479373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290662545447/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((479373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c69 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-2934/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3487699/5000000) (δ := 6529/500000000) (ψ := -133673/1000000) 259 175
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t69 : ((-113033933087/1000000000000 : ℚ) : ℝ) ≤ stT259 69 := by
  have hc : ((-93893/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113033933087/1000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-93893/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c70 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((2963/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 468257/2000000) (δ := 6479/500000000) (ψ := -133673/1000000) 259 175
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t70 : ((3541161757/50000000000 : ℚ) : ℝ) ≤ stT259 70 := by
  have hc : ((11851/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3541161757/50000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((11851/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c71 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-101887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83643/200000) (δ := 6519/500000000) (ψ := -133673/1000000) 259 176
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t71 : ((-60488498367/5000000000000 : ℚ) : ℝ) ≤ stT259 71 := by
  have hc : ((-101937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60488498367/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-101937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c72 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-369801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4873979/10000000) (δ := 6569/500000000) (ψ := -133673/1000000) 259 176
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t72 : ((-27242115107/625000000000 : ℚ) : ℝ) ≤ stT259 72 := by
  have hc : ((-369851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27242115107/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-369851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c73 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((362029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -951411/5000000) (δ := 3243/250000000) (ψ := -133673/1000000) 259 177
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t73 : ((105923365911/1250000000000 : ℚ) : ℝ) ≤ stT259 73 := by
  have hc : ((90501/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105923365911/1250000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((90501/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c74 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-929083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726701/2500000) (δ := 3243/250000000) (ψ := -133673/1000000) 259 177
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t74 : ((-1080095742441/10000000000000 : ℚ) : ℝ) ≤ stT259 74 := by
  have hc : ((-929133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1080095742441/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-929133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c75 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((999037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54851/5000000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 178
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t75 : ((11535302889/100000000000 : ℚ) : ℝ) ≤ stT259 75 := by
  have hc : ((998987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11535302889/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((998987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c76 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-970129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3620699/5000000) (δ := 13087/1000000000) (ψ := -133673/1000000) 259 179
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t76 : ((-1112871957141/10000000000000 : ℚ) : ℝ) ≤ stT259 76 := by
  have hc : ((-970179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1112871957141/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-970179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c77 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((882749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 611393/5000000) (δ := 3279/250000000) (ψ := -133673/1000000) 259 179
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t77 : ((201185638779/2000000000000 : ℚ) : ℝ) ≤ stT259 77 := by
  have hc : ((882699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201185638779/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((882699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c78 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-385781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245209/400000) (δ := 6547/500000000) (ψ := -133673/1000000) 259 180
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t78 : ((-109209911517/1250000000000 : ℚ) : ℝ) ≤ stT259 78 := by
  have hc : ((-192903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109209911517/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-192903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c79 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((662001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2118277/10000000) (δ := 13009/1000000000) (ψ := -133673/1000000) 259 180
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t79 : ((744752464737/10000000000000 : ℚ) : ℝ) ≤ stT259 79 := by
  have hc : ((661951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((744752464737/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((661951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c80 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-114109/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5444913/10000000) (δ := 13001/1000000000) (ψ := -133673/1000000) 259 181
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t80 : ((-63794461023/1000000000000 : ℚ) : ℝ) ≤ stT259 80 := by
  have hc : ((-114119/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63794461023/1000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-114119/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c81 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((126671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20302/78125) (δ := 13101/1000000000) (ψ := -133673/1000000) 259 181
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t81 : ((281463305187/5000000000000 : ℚ) : ℝ) ≤ stT259 81 := by
  have hc : ((253317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281463305187/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((253317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c82 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-237503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2582209/5000000) (δ := 2599/200000000) (ψ := -133673/1000000) 259 182
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t82 : ((-8197061589/156250000000 : ℚ) : ℝ) ≤ stT259 82 := by
  have hc : ((-29691/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8197061589/156250000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-29691/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c83 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((476897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2684189/10000000) (δ := 3277/250000000) (ψ := -133673/1000000) 259 182
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t83 : ((261703647387/5000000000000 : ℚ) : ℝ) ≤ stT259 83 := by
  have hc : ((476847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261703647387/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((476847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c84 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-511467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2634609/5000000) (δ := 3261/125000000) (ψ := -133673/1000000) 259 183
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t84 : ((-55811108353/1000000000000 : ℚ) : ℝ) ≤ stT259 84 := by
  have hc : ((-511517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55811108353/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-511517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c85 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((575619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2393589/10000000) (δ := 2603/200000000) (ψ := -133673/1000000) 259 183
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t85 : ((156073016747/2500000000000 : ℚ) : ℝ) ≤ stT259 85 := by
  have hc : ((575569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156073016747/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((575569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c86 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-663651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2870607/5000000) (δ := 13123/1000000000) (ψ := -133673/1000000) 259 184
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t86 : ((-89460921491/1250000000000 : ℚ) : ℝ) ≤ stT259 86 := by
  have hc : ((-663701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89460921491/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-663701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c87 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((383133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 436117/2500000) (δ := 327/25000000) (ψ := -133673/1000000) 259 184
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t87 : ((6417729439/78125000000 : ℚ) : ℝ) ≤ stT259 87 := by
  have hc : ((95777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6417729439/78125000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((95777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c88 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-869687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1640853/2500000) (δ := 13073/1000000000) (ψ := -133673/1000000) 259 185
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t88 : ((-231785780237/2500000000000 : ℚ) : ℝ) ≤ stT259 88 := by
  have hc : ((-869737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231785780237/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-869737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c89 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((954979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150603/2000000) (δ := 1313/100000000) (ψ := -133673/1000000) 259 185
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t89 : ((1012221875213/10000000000000 : ℚ) : ℝ) ≤ stT259 89 := by
  have hc : ((954929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1012221875213/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((954929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c90 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-998569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7720237/10000000) (δ := 6483/500000000) (ψ := -133673/1000000) 259 186
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t90 : ((-1052637297567/10000000000000 : ℚ) : ℝ) ≤ stT259 90 := by
  have hc : ((-998619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1052637297567/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-998619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c91 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((974529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -565459/10000000) (δ := 25937/1000000000) (ψ := -133673/1000000) 259 186
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t91 : ((255382686009/2500000000000 : ℚ) : ℝ) ≤ stT259 91 := by
  have hc : ((974479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255382686009/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((974479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c92 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-859169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6511101/10000000) (δ := 13037/1000000000) (ψ := -133673/1000000) 259 186
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t92 : ((-895798530487/10000000000000 : ℚ) : ℝ) ≤ stT259 92 := by
  have hc : ((-859219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-895798530487/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-859219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c93 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((79767/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -439361/2000000) (δ := 13059/1000000000) (ψ := -133673/1000000) 259 187
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t93 : ((330831957893/5000000000000 : ℚ) : ℝ) ≤ stT259 93 := by
  have hc : ((319043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330831957893/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((319043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c94 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-157551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2364201/5000000) (δ := 12959/1000000000) (ψ := -133673/1000000) 259 187
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t94 : ((-10157959567/312500000000 : ℚ) : ℝ) ≤ stT259 94 := by
  have hc : ((-19697/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10157959567/312500000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-19697/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c95 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-40089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4127651/10000000) (δ := 13151/1000000000) (ψ := -133673/1000000) 259 188
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t95 : ((-20578060803/2500000000000 : ℚ) : ℝ) ≤ stT259 95 := by
  have hc : ((-20057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20578060803/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-20057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c96 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((243997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530503/2000000) (δ := 3263/250000000) (ψ := -133673/1000000) 259 188
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t96 : ((3112533783/62500000000 : ℚ) : ℝ) ≤ stT259 96 := by
  have hc : ((60993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3112533783/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((60993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c97 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-823423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1269107/2000000) (δ := 6479/500000000) (ψ := -133673/1000000) 259 189
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t97 : ((-836110840131/10000000000000 : ℚ) : ℝ) ≤ stT259 97 := by
  have hc : ((-823473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-836110840131/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-823473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c98 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((49651/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 295549/10000000) (δ := 6529/500000000) (ψ := -133673/1000000) 259 189
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t98 : ((12538132893/125000000000 : ℚ) : ℝ) ≤ stT259 98 := by
  have hc : ((99297/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12538132893/125000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((99297/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c99 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-923419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1717307/2500000) (δ := 6529/500000000) (ψ := -133673/1000000) 259 189
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t99 : ((-464060718411/5000000000000 : ℚ) : ℝ) ≤ stT259 99 := by
  have hc : ((-923469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464060718411/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-923469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c100 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((119171/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1165583/5000000) (δ := 6533/500000000) (ψ := -133673/1000000) 259 190
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t100 : ((119160880839/2000000000000 : ℚ) : ℝ) ≤ stT259 100 := by
  have hc : ((119161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119160880839/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((119161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c101 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-2307/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2055859/5000000) (δ := 6533/500000000) (ψ := -133673/1000000) 259 190
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t101 : ((-18376859303/2500000000000 : ℚ) : ℝ) ≤ stT259 101 := by
  have hc : ((-36937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18376859303/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-36937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c102 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-493367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5216881/10000000) (δ := 13073/1000000000) (ψ := -133673/1000000) 259 191
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t102 : ((-122138963929/2500000000000 : ℚ) : ℝ) ≤ stT259 102 := by
  have hc : ((-493417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122138963929/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-493417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c103 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((904719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1100193/10000000) (δ := 1313/100000000) (ψ := -133673/1000000) 259 191
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t103 : ((891396601101/10000000000000 : ℚ) : ℝ) ≤ stT259 103 := by
  have hc : ((904669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((891396601101/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((904669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c104 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-122531/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3678137/5000000) (δ := 13073/1000000000) (ψ := -133673/1000000) 259 191
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t104 : ((-480630796569/5000000000000 : ℚ) : ℝ) ≤ stT259 104 := by
  have hc : ((-490149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-480630796569/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-490149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c105 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((650787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1077719/5000000) (δ := 327/25000000) (ψ := -133673/1000000) 259 192
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t105 : ((6350542383/100000000000 : ℚ) : ℝ) ≤ stT259 105 := by
  have hc : ((650737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6350542383/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((650737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c106 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-2201/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 199101/500000) (δ := 649/50000000) (ψ := -133673/1000000) 259 192
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t106 : ((-535664229/250000000000 : ℚ) : ℝ) ≤ stT259 106 := by
  have hc : ((-1103/50000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-535664229/250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-1103/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c107 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-317351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176439/312500) (δ := 1627/125000000) (ψ := -133673/1000000) 259 193
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t107 : ((-4794048783/78125000000 : ℚ) : ℝ) ≤ stT259 107 := by
  have hc : ((-9918/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4794048783/78125000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-9918/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c108 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((247159/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47157/1250000) (δ := 1627/125000000) (ψ := -133673/1000000) 259 193
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t108 : ((1902533757/20000000000 : ℚ) : ℝ) ≤ stT259 108 := by
  have hc : ((494293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1902533757/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((494293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c109 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-823303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1269001/2000000) (δ := 13087/1000000000) (ψ := -133673/1000000) 259 193
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t109 : ((-788629733931/10000000000000 : ℚ) : ℝ) ≤ stT259 109 := by
  have hc : ((-823353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-788629733931/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-823353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c110 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((47443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -689933/2000000) (δ := 13009/1000000000) (ψ := -133673/1000000) 259 194
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t110 : ((45223179391/2500000000000 : ℚ) : ℝ) ≤ stT259 110 := by
  have hc : ((94861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45223179391/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((94861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c111 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((570191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 482029/2000000) (δ := 13109/1000000000) (ψ := -133673/1000000) 259 194
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t111 : ((541153321137/10000000000000 : ℚ) : ℝ) ≤ stT259 111 := by
  have hc : ((570141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541153321137/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((570141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c112 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-494729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7490649/10000000) (δ := 6551/500000000) (ψ := -133673/1000000) 259 195
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t112 : ((-14609343489/156250000000 : ℚ) : ℝ) ≤ stT259 112 := by
  have hc : ((-247377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14609343489/156250000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-247377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c113 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((48043/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867511/5000000) (δ := 13001/1000000000) (ψ := -133673/1000000) 259 195
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t113 : ((4519207121/62500000000 : ℚ) : ℝ) ≤ stT259 113 := by
  have hc : ((384319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4519207121/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((384319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c114 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-857/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1984921/5000000) (δ := 6551/500000000) (ψ := -133673/1000000) 259 195
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t114 : ((-804995667/500000000000 : ℚ) : ℝ) ≤ stT259 114 := by
  have hc : ((-1719/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-804995667/500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-1719/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c115 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-379711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6083051/10000000) (δ := 6497/500000000) (ψ := -133673/1000000) 259 196
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t115 : ((-8852642967/125000000000 : ℚ) : ℝ) ≤ stT259 115 := by
  have hc : ((-47467/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8852642967/125000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-47467/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c116 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((981853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119249/2500000) (δ := 6497/500000000) (ψ := -133673/1000000) 259 196
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t116 : ((227895130557/2500000000000 : ℚ) : ℝ) ≤ stT259 116 := by
  have hc : ((981803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227895130557/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((981803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c117 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-44539/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1016203/2000000) (δ := 13109/1000000000) (ψ := -133673/1000000) 259 196
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t117 : ((-80431587/1953125000 : ℚ) : ℝ) ≤ stT259 117 := by
  have hc : ((-1392/3125 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80431587/1953125000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-1392/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c118 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-457971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -511627/1000000) (δ := 3279/250000000) (ψ := -133673/1000000) 259 197
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t118 : ((-16865707283/400000000000 : ℚ) : ℝ) ≤ stT259 118 := by
  have hc : ((-458021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16865707283/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-458021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c119 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((198067/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 347853/10000000) (δ := 3279/250000000) (ψ := -133673/1000000) 259 197
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t119 : ((90779227893/1000000000000 : ℚ) : ℝ) ≤ stT259 119 := by
  have hc : ((198057/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90779227893/1000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((198057/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c120 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-167783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5766327/10000000) (δ := 1627/125000000) (ψ := -133673/1000000) 259 197
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t120 : ((-306351291761/5000000000000 : ℚ) : ℝ) ≤ stT259 120 := by
  have hc : ((-335591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306351291761/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-335591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c121 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-253667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4568163/10000000) (δ := 13123/1000000000) (ψ := -133673/1000000) 259 198
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t121 : ((-230651841247/10000000000000 : ℚ) : ℝ) ≤ stT259 121 := by
  have hc : ((-253717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230651841247/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-253717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c122 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((954017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 152217/2000000) (δ := 327/25000000) (ψ := -133673/1000000) 259 198
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t122 : ((863680701219/10000000000000 : ℚ) : ℝ) ≤ stT259 122 := by
  have hc : ((953967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((863680701219/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((953967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c123 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-374957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3023411/5000000) (δ := 649/50000000) (ψ := -133673/1000000) 259 198
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t123 : ((-16905500997/250000000000 : ℚ) : ℝ) ≤ stT259 123 := by
  have hc : ((-187491/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16905500997/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-187491/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c124 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-195223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1104551/2500000) (δ := 1303/100000000) (ψ := -133673/1000000) 259 199
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t124 : ((-175360426371/10000000000000 : ℚ) : ℝ) ≤ stT259 124 := by
  have hc : ((-195273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175360426371/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-195273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c125 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((237849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156529/2000000) (δ := 13073/1000000000) (ψ := -133673/1000000) 259 199
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t125 : ((425454774371/5000000000000 : ℚ) : ℝ) ≤ stT259 125 := by
  have hc : ((475673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425454774371/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((475673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c126 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-721541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1188411/2000000) (δ := 1303/100000000) (ψ := -133673/1000000) 259 199
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t126 : ((-642844495761/10000000000000 : ℚ) : ℝ) ≤ stT259 126 := by
  have hc : ((-721591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-642844495761/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-721591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c127 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-11367/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1161839/2500000) (δ := 13037/1000000000) (ψ := -133673/1000000) 259 200
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t127 : ((-10088361733/400000000000 : ℚ) : ℝ) ≤ stT259 127 := by
  have hc : ((-11369/40000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10088361733/400000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-11369/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c128 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((61573/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107779/2500000) (δ := 13037/1000000000) (ψ := -133673/1000000) 259 200
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t128 : ((435364526597/5000000000000 : ℚ) : ℝ) ≤ stT259 128 := by
  have hc : ((492559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((435364526597/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((492559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c129 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-289393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547009/1000000) (δ := 6533/500000000) (ψ := -133673/1000000) 259 200
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t129 : ((-127409183759/2500000000000 : ℚ) : ℝ) ≤ stT259 129 := by
  have hc : ((-144709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127409183759/2500000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-144709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c130 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-100131/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2618939/5000000) (δ := 6479/500000000) (ψ := -133673/1000000) 259 201
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t130 : ((-87829565319/2000000000000 : ℚ) : ℝ) ≤ stT259 130 := by
  have hc : ((-100141/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87829565319/2000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-100141/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c131 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((198781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5523/200000) (δ := 2609/200000000) (ψ := -133673/1000000) 259 201
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t131 : ((21708377223/250000000000 : ℚ) : ℝ) ≤ stT259 131 := by
  have hc : ((198771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21708377223/250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((198771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c132 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-71089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1161957/2500000) (δ := 6529/500000000) (ψ := -133673/1000000) 259 201
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t132 : ((-123771926967/5000000000000 : ℚ) : ℝ) ≤ stT259 132 := by
  have hc : ((-142203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123771926967/5000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-142203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c133 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-391207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6173323/10000000) (δ := 1619/125000000) (ψ := -133673/1000000) 259 202
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t133 : ((-530064343/7812500000 : ℚ) : ℝ) ≤ stT259 133 := by
  have hc : ((-12226/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530064343/7812500000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-12226/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c134 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((431593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1323127/10000000) (δ := 811/31250000) (ψ := -133673/1000000) 259 202
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t134 : ((5825277891/78125000000 : ℚ) : ℝ) ≤ stT259 134 := by
  have hc : ((26973/31250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5825277891/78125000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((26973/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c135 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((21689/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3491003/10000000) (δ := 1619/125000000) (ψ := -133673/1000000) 259 202
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t135 : ((37323037961/2500000000000 : ℚ) : ℝ) ≤ stT259 135 := by
  have hc : ((86731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37323037961/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((86731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c136 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-246553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3719173/5000000) (δ := 1643/125000000) (ψ := -133673/1000000) 259 203
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t136 : ((-422856380583/5000000000000 : ℚ) : ℝ) ≤ stT259 136 := by
  have hc : ((-493131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422856380583/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-493131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c137 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((236599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336837/1250000) (δ := 3261/250000000) (ψ := -133673/1000000) 259 203
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t137 : ((101059326459/2500000000000 : ℚ) : ℝ) ≤ stT259 137 := by
  have hc : ((118287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101059326459/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((118287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c138 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((69257/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2014377/10000000) (δ := 1643/125000000) (ψ := -133673/1000000) 259 203
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t138 : ((1842224391/31250000000 : ℚ) : ℝ) ≤ stT259 138 := by
  have hc : ((17313/25000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1842224391/31250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((17313/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c139 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-89347/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3344761/5000000) (δ := 13059/1000000000) (ψ := -133673/1000000) 259 203
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t139 : ((-9473422941/125000000000 : ℚ) : ℝ) ≤ stT259 139 := by
  have hc : ((-11169/12500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9473422941/125000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-11169/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c140 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-178969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2188419/5000000) (δ := 13037/1000000000) (ψ := -133673/1000000) 259 204
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t140 : ((-30259760589/2000000000000 : ℚ) : ℝ) ≤ stT259 140 := by
  have hc : ((-179019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30259760589/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-179019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c141 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((995709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231679/10000000) (δ := 6533/500000000) (ψ := -133673/1000000) 259 204
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t141 : ((838495222509/10000000000000 : ℚ) : ℝ) ≤ stT259 141 := by
  have hc : ((995659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((838495222509/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((995659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c142 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-345039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4807691/10000000) (δ := 6533/500000000) (ψ := -133673/1000000) 259 204
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t142 : ((-144796238599/5000000000000 : ℚ) : ℝ) ≤ stT259 142 := by
  have hc : ((-345089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144796238599/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-345089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c143 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-206469/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6356377/10000000) (δ := 1313/100000000) (ψ := -133673/1000000) 259 205
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t143 : ((-345337418009/5000000000000 : ℚ) : ℝ) ≤ stT259 143 := by
  have hc : ((-412963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345337418009/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-412963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c144 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((740029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115263/625000) (δ := 12973/1000000000) (ψ := -133673/1000000) 259 205
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t144 : ((616648920007/10000000000000 : ℚ) : ℝ) ≤ stT259 144 := by
  have hc : ((739979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((616648920007/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((739979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c145 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((246733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164801/625000) (δ := 13073/1000000000) (ψ := -133673/1000000) 259 205
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t145 : ((25609955679/625000000000 : ℚ) : ℝ) ≤ stT259 145 := by
  have hc : ((61677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25609955679/625000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((61677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c146 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-953309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3543509/5000000) (δ := 1313/100000000) (ψ := -133673/1000000) 259 205
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t146 : ((-394502814277/5000000000000 : ℚ) : ℝ) ≤ stT259 146 := by
  have hc : ((-953359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394502814277/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-953359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c147 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-54727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168047/400000) (δ := 13123/1000000000) (ψ := -133673/1000000) 259 206
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t147 : ((-1411210557/156250000000 : ℚ) : ℝ) ≤ stT259 147 := by
  have hc : ((-1711/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1411210557/156250000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-1711/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c148 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((997153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188681/10000000) (δ := 13023/1000000000) (ψ := -133673/1000000) 259 206
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t148 : ((409806341691/5000000000000 : ℚ) : ℝ) ≤ stT259 148 := by
  have hc : ((997103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409806341691/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((997103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c149 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-246249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4549011/10000000) (δ := 649/50000000) (ψ := -133673/1000000) 259 206
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t149 : ((-6305500699/312500000000 : ℚ) : ℝ) ≤ stT259 149 := by
  have hc : ((-246299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6305500699/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-246299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c150 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-916947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -682789/1000000) (δ := 2623/200000000) (ψ := -133673/1000000) 259 207
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t150 : ((-748725299509/10000000000000 : ℚ) : ℝ) ≤ stT259 150 := by
  have hc : ((-916997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-748725299509/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-916997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c151 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((66461/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2525511/10000000) (δ := 3247/250000000) (ψ := -133673/1000000) 259 207
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t151 : ((54080078093/1250000000000 : ℚ) : ℝ) ≤ stT259 151 := by
  have hc : ((265819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54080078093/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((265819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c152 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((191311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 874221/5000000) (δ := 2603/200000000) (ψ := -133673/1000000) 259 207
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t152 : ((310327104879/5000000000000 : ℚ) : ℝ) ≤ stT259 152 := by
  have hc : ((382597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310327104879/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((382597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c153 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-183967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5994359/10000000) (δ := 409/31250000) (ψ := -133673/1000000) 259 207
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t153 : ((-297477557427/5000000000000 : ℚ) : ℝ) ≤ stT259 153 := by
  have hc : ((-367959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297477557427/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-367959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c154 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-36687/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686917/1250000) (δ := 2619/200000000) (ψ := -133673/1000000) 259 208
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t154 : ((-236525972783/5000000000000 : ℚ) : ℝ) ≤ stT259 154 := by
  have hc : ((-293521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236525972783/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-293521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c155 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((173389/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1304393/10000000) (δ := 3277/250000000) (ψ := -133673/1000000) 259 208
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t155 : ((139261307001/2000000000000 : ℚ) : ℝ) ≤ stT259 155 := by
  have hc : ((173379/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139261307001/2000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((173379/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c156 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((414097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 571923/2000000) (δ := 813/62500000) (ψ := -133673/1000000) 259 208
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t156 : ((517972797/15625000000 : ℚ) : ℝ) ≤ stT259 156 := by
  have hc : ((414047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517972797/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((414047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c157 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-941821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6997011/10000000) (δ := 2619/200000000) (ψ := -133673/1000000) 259 208
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t157 : ((-751695000777/10000000000000 : ℚ) : ℝ) ≤ stT259 157 := by
  have hc : ((-941871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-751695000777/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-941871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c158 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-16619/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2299923/5000000) (δ := 13101/1000000000) (ψ := -133673/1000000) 259 209
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t158 : ((-52895458083/2500000000000 : ℚ) : ℝ) ≤ stT259 158 := by
  have hc : ((-132977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52895458083/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-132977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c159 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((489443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -514639/10000000) (δ := 13101/1000000000) (ψ := -133673/1000000) 259 209
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t159 : ((194066717159/2500000000000 : ℚ) : ℝ) ≤ stT259 159 := by
  have hc : ((244709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194066717159/2500000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((244709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c160 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((152231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3544927/10000000) (δ := 13101/1000000000) (ψ := -133673/1000000) 259 209
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t160 : ((120309580989/10000000000000 : ℚ) : ℝ) ≤ stT259 160 := by
  have hc : ((152181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120309580989/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((152181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c161 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-198793/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 947397/1250000) (δ := 13001/1000000000) (ψ := -133673/1000000) 259 209
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t161 : ((-156678831133/2000000000000 : ℚ) : ℝ) ≤ stT259 161 := by
  have hc : ((-198803/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156678831133/2000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-198803/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c162 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-38457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4119467/10000000) (δ := 13009/1000000000) (ψ := -133673/1000000) 259 210
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t162 : ((-604686907/100000000000 : ℚ) : ℝ) ≤ stT259 162 := by
  have hc : ((-19241/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604686907/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-19241/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c163 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((499273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134817/10000000) (δ := 6497/500000000) (ψ := -133673/1000000) 259 210
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t163 : ((1222003089/15625000000 : ℚ) : ℝ) ≤ stT259 163 := by
  have hc : ((31203/31250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1222003089/15625000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((31203/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c164 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((5077/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3825423/10000000) (δ := 13109/1000000000) (ψ := -133673/1000000) 259 210
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t164 : ((3959586411/1250000000000 : ℚ) : ℝ) ≤ stT259 164 := by
  have hc : ((20283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3959586411/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((20283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c165 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-999317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310463/400000) (δ := 6497/500000000) (ψ := -133673/1000000) 259 210
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t165 : ((-778006210133/10000000000000 : ℚ) : ℝ) ≤ stT259 165 := by
  have hc : ((-999367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778006210133/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-999367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c166 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-4279/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4033999/10000000) (δ := 12987/1000000000) (ψ := -133673/1000000) 259 211
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t166 : ((-831257721/250000000000 : ℚ) : ℝ) ≤ stT259 166 := by
  have hc : ((-1071/25000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-831257721/250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-1071/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c167 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((998317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145049/10000000) (δ := 1627/125000000) (ψ := -133673/1000000) 259 211
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t167 : ((772481964741/10000000000000 : ℚ) : ℝ) ≤ stT259 167 := by
  have hc : ((998267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((772481964741/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((998267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c168 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((41233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3720591/10000000) (δ := 3279/250000000) (ψ := -133673/1000000) 259 211
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t168 : ((993519729/156250000000 : ℚ) : ℝ) ≤ stT259 168 := by
  have hc : ((5151/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((993519729/156250000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((5151/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c169 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-993251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3781687/5000000) (δ := 3279/250000000) (ψ := -133673/1000000) 259 211
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t169 : ((-764077921531/10000000000000 : ℚ) : ℝ) ≤ stT259 169 := by
  have hc : ((-993301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-764077921531/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-993301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c170 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-39587/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2162267/5000000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 212
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t170 : ((-12148572207/1000000000000 : ℚ) : ℝ) ≤ stT259 170 := by
  have hc : ((-79199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12148572207/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-79199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c171 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((488937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -263441/5000000) (δ := 13079/1000000000) (ψ := -133673/1000000) 259 212
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t171 : ((23367518483/312500000000 : ℚ) : ℝ) ≤ stT259 171 := by
  have hc : ((30557/31250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23367518483/312500000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((30557/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c172 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((67007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1624313/5000000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 212
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t172 : ((25541385147/1250000000000 : ℚ) : ℝ) ≤ stT259 172 := by
  have hc : ((133989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25541385147/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((133989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c173 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-942523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 875281/1250000) (δ := 13079/1000000000) (ψ := -133673/1000000) 259 212
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t173 : ((-358312527939/5000000000000 : ℚ) : ℝ) ≤ stT259 173 := by
  have hc : ((-942573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358312527939/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-942573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c174 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-81313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4973719/10000000) (δ := 13031/1000000000) (ψ := -133673/1000000) 259 213
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t174 : ((-61650884977/2000000000000 : ℚ) : ℝ) ≤ stT259 174 := by
  have hc : ((-81323/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61650884977/2000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-81323/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c175 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((43753/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263091/10000000) (δ := 3243/250000000) (ψ := -133673/1000000) 259 213
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t175 : ((8268056991/125000000000 : ℚ) : ℝ) ≤ stT259 175 := by
  have hc : ((87501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8268056991/125000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((87501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c176 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((564849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606591/2500000) (δ := 3243/250000000) (ψ := -133673/1000000) 259 213
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t176 : ((212866530311/5000000000000 : ℚ) : ℝ) ≤ stT259 176 := by
  have hc : ((564799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212866530311/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((564799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c177 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-152503/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609497/1000000) (δ := 13131/1000000000) (ψ := -133673/1000000) 259 213
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t177 : ((-114635938911/2000000000000 : ℚ) : ℝ) ≤ stT259 177 := by
  have hc : ((-152513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114635938911/2000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-152513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c178 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-145579/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1491277/2500000) (δ := 6519/500000000) (ψ := -133673/1000000) 259 214
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t178 : ((-27280903587/500000000000 : ℚ) : ℝ) ≤ stT259 178 := by
  have hc : ((-145589/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27280903587/500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-145589/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c179 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((29689/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2337619/10000000) (δ := 2593/200000000) (ψ := -133673/1000000) 259 214
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t179 : ((8875491651/200000000000 : ℚ) : ℝ) ≤ stT259 179 := by
  have hc : ((59373/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8875491651/200000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((59373/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c180 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((218449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317401/2500000) (δ := 6569/500000000) (ψ := -133673/1000000) 259 214
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t180 : ((65125094983/1000000000000 : ℚ) : ℝ) ≤ stT259 180 := by
  have hc : ((436873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65125094983/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((436873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c181 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-363439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4856883/10000000) (δ := 2593/200000000) (ψ := -133673/1000000) 259 214
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t181 : ((-54035911251/2000000000000 : ℚ) : ℝ) ≤ stT259 181 := by
  have hc : ((-363489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54035911251/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-363489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c182 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-974087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3641807/5000000) (δ := 2609/200000000) (ψ := -133673/1000000) 259 215
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t182 : ((-577663241/8000000000 : ℚ) : ℝ) ≤ stT259 182 := by
  have hc : ((-974137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-577663241/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-974137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c183 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((38233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1867819/5000000) (δ := 6479/500000000) (ψ := -133673/1000000) 259 215
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t183 : ((441314937/78125000000 : ℚ) : ℝ) ≤ stT259 183 := by
  have hc : ((1194/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441314937/78125000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((1194/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c184 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((996573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -103511/5000000) (δ := 6479/500000000) (ψ := -133673/1000000) 259 215
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t184 : ((734645724307/10000000000000 : ℚ) : ℝ) ≤ stT259 184 := by
  have hc : ((996523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734645724307/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((996523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c185 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((247209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3302493/10000000) (δ := 2609/200000000) (ψ := -133673/1000000) 259 215
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t185 : ((90857378513/5000000000000 : ℚ) : ℝ) ≤ stT259 185 := by
  have hc : ((247159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90857378513/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((247159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c186 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-182259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1698259/2500000) (δ := 2609/200000000) (ψ := -133673/1000000) 259 215
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t186 : ((-33411548121/500000000000 : ℚ) : ℝ) ≤ stT259 186 := by
  have hc : ((-182269/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33411548121/500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-182269/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c187 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-569927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5443033/10000000) (δ := 13151/1000000000) (ψ := -133673/1000000) 259 216
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t187 : ((-416808790721/10000000000000 : ℚ) : ℝ) ≤ stT259 187 := by
  have hc : ((-569977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416808790721/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-569977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c188 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((13993/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1989721/10000000) (δ := 13051/1000000000) (ψ := -133673/1000000) 259 216
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t188 : ((318896919/6250000000 : ℚ) : ℝ) ≤ stT259 188 := by
  have hc : ((1749/2500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318896919/6250000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((1749/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c189 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((167497/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1445331/10000000) (δ := 13151/1000000000) (ψ := -133673/1000000) 259 216
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t189 : ((3807146997/62500000000 : ℚ) : ℝ) ≤ stT259 189 := by
  have hc : ((167487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3807146997/62500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((167487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c190 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-45677/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4862189/10000000) (δ := 1619/125000000) (ψ := -133673/1000000) 259 216
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t190 : ((-132568588641/5000000000000 : ℚ) : ℝ) ≤ stT259 190 := by
  have hc : ((-182733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132568588641/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-182733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c191 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-197353/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1861697/2500000) (δ := 3261/250000000) (ψ := -133673/1000000) 259 217
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t191 : ((-5712277309/80000000000 : ℚ) : ℝ) ≤ stT259 191 := by
  have hc : ((-197363/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5712277309/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-197363/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c192 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-27709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -508201/1250000) (δ := 1643/125000000) (ψ := -133673/1000000) 259 217
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t192 : ((-1250955937/312500000000 : ℚ) : ℝ) ≤ stT259 192 := by
  have hc : ((-13867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1250955937/312500000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-13867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c193 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((960837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28079/400000) (δ := 1643/125000000) (ψ := -133673/1000000) 259 217
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t193 : ((138317778881/2000000000000 : ℚ) : ℝ) ≤ stT259 193 := by
  have hc : ((960787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138317778881/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((960787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c194 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((245429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 528861/2000000) (δ := 1643/125000000) (ψ := -133673/1000000) 259 217
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t194 : ((22023720629/625000000000 : ℚ) : ℝ) ≤ stT259 194 := by
  have hc : ((61351/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22023720629/625000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((61351/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c195 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-146031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2986681/5000000) (δ := 12959/1000000000) (ψ := -133673/1000000) 259 217
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t195 : ((-20916430143/400000000000 : ℚ) : ℝ) ≤ stT259 195 := by
  have hc : ((-146041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20916430143/400000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-146041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c196 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-168103/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3211287/5000000) (δ := 12967/1000000000) (ψ := -133673/1000000) 259 218
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t196 : ((-60040381159/1000000000000 : ℚ) : ℝ) ≤ stT259 196 := by
  have hc : ((-168113/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60040381159/1000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-168113/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c197 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((157209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1563691/5000000) (δ := 3259/250000000) (ψ := -133673/1000000) 259 218
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t197 : ((21872829/976562500 : ℚ) : ℝ) ≤ stT259 197 := by
  have hc : ((4912/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21872829/976562500 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((4912/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c198 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((499087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30221/2000000) (δ := 12967/1000000000) (ψ := -133673/1000000) 259 218
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t198 : ((177333946239/2500000000000 : ℚ) : ℝ) ≤ stT259 198 := by
  have hc : ((249531/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177333946239/2500000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((249531/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c199 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((5103/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85327/250000) (δ := 821/62500000) (ψ := -133673/1000000) 259 218
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t199 : ((14466134567/1000000000000 : ℚ) : ℝ) ≤ stT259 199 := by
  have hc : ((20407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14466134567/1000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((20407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c200 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-44393/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3329337/5000000) (δ := 3259/250000000) (ψ := -133673/1000000) 259 218
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t200 : ((-62784737637/1000000000000 : ℚ) : ℝ) ≤ stT259 200 := by
  have hc : ((-88791/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62784737637/1000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-88791/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c201 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-686839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2909909/5000000) (δ := 6487/500000000) (ψ := -133673/1000000) 259 219
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t201 : ((-242247204297/5000000000000 : ℚ) : ℝ) ≤ stT259 201 := by
  have hc : ((-686889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242247204297/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-686889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c202 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((503987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -260647/1000000) (δ := 13029/1000000000) (ψ := -133673/1000000) 259 219
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t202 : ((354568561389/10000000000000 : ℚ) : ℝ) ≤ stT259 202 := by
  have hc : ((503937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((354568561389/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((503937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c203 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((48609/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591079/10000000) (δ := 13129/1000000000) (ψ := -133673/1000000) 259 219
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t203 : ((34115055303/500000000000 : ℚ) : ℝ) ≤ stT259 203 := by
  have hc : ((97213/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34115055303/500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((97213/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c204 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((77/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1886447/5000000) (δ := 13129/1000000000) (ψ := -133673/1000000) 259 219
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t204 : ((43093617/10000000000 : ℚ) : ℝ) ≤ stT259 204 := by
  have hc : ((1231/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43093617/10000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((1231/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c205 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-933793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6939169/10000000) (δ := 13129/1000000000) (ψ := -133673/1000000) 259 219
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t205 : ((-652224900333/10000000000000 : ℚ) : ℝ) ≤ stT259 205 := by
  have hc : ((-933843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-652224900333/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-933843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c206 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-62597/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5617929/10000000) (δ := 13081/1000000000) (ψ := -133673/1000000) 259 220
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t206 : ((-10904235467/250000000000 : ℚ) : ℝ) ≤ stT259 206 := by
  have hc : ((-31301/50000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10904235467/250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-31301/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c207 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((546231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1241173/5000000) (δ := 6511/500000000) (ψ := -133673/1000000) 259 220
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t207 : ((47452751461/1250000000000 : ℚ) : ℝ) ≤ stT259 207 := by
  have hc : ((546181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47452751461/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((546181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c208 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((483799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 638151/10000000) (δ := 12981/1000000000) (ψ := -133673/1000000) 259 220
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t208 : ((1341747189/20000000000 : ℚ) : ℝ) ≤ stT259 208 := by
  have hc : ((241887/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1341747189/20000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((241887/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c209 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((14651/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 374369/1000000) (δ := 6561/500000000) (ψ := -133673/1000000) 259 220
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t209 : ((5063692337/1000000000000 : ℚ) : ℝ) ≤ stT259 209 := by
  have hc : ((14641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5063692337/1000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((14641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c210 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-917983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3417201/5000000) (δ := 6511/500000000) (ψ := -133673/1000000) 259 220
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t210 : ((-316751680089/5000000000000 : ℚ) : ℝ) ≤ stT259 210 := by
  have hc : ((-918033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316751680089/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-918033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c211 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-680337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1449387/2500000) (δ := 2623/200000000) (ψ := -133673/1000000) 259 221
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t211 : ((-468398142023/10000000000000 : ℚ) : ℝ) ≤ stT259 211 := by
  have hc : ((-680387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468398142023/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-680387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c212 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((458543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2736103/10000000) (δ := 2603/200000000) (ψ := -133673/1000000) 259 221
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t212 : ((157446954693/5000000000000 : ℚ) : ℝ) ≤ stT259 212 := by
  have hc : ((458493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157446954693/5000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((458493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c213 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((496137/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310967/10000000) (δ := 2623/200000000) (ψ := -133673/1000000) 259 221
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t213 : ((5311406079/78125000000 : ℚ) : ℝ) ≤ stT259 213 := by
  have hc : ((31007/31250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5311406079/78125000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((31007/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c214 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((231169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3343793/10000000) (δ := 409/31250000) (ψ := -133673/1000000) 259 221
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t214 : ((31597896323/2000000000000 : ℚ) : ℝ) ≤ stT259 214 := by
  have hc : ((231119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31597896323/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((231119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c215 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-827241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3181219/5000000) (δ := 409/31250000) (ψ := -133673/1000000) 259 221
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t215 : ((-112841665109/2000000000000 : ℚ) : ℝ) ≤ stT259 215 := by
  have hc : ((-827291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112841665109/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-827291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c216 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-411181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6340867/10000000) (δ := 3277/250000000) (ψ := -133673/1000000) 259 222
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t216 : ((-69947579821/1250000000000 : ℚ) : ℝ) ≤ stT259 216 := by
  have hc : ((-205603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69947579821/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-205603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c217 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((228703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3350129/10000000) (δ := 813/62500000) (ψ := -133673/1000000) 259 222
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t217 : ((38804929283/2500000000000 : ℚ) : ℝ) ≤ stT259 217 := by
  have hc : ((228653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38804929283/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((228653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c218 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((988883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186559/5000000) (δ := 2599/200000000) (ψ := -133673/1000000) 259 222
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t218 : ((133944351681/2000000000000 : ℚ) : ℝ) ≤ stT259 218 := by
  have hc : ((988833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133944351681/2000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((988833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c219 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((127391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518059/2000000) (δ := 813/62500000) (ψ := -133673/1000000) 259 222
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t219 : ((172148730909/5000000000000 : ℚ) : ℝ) ≤ stT259 219 := by
  have hc : ((254757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172148730909/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((254757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c220 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-601417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346261/625000) (δ := 2619/200000000) (ψ := -133673/1000000) 259 222
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t220 : ((-2027545257/50000000000 : ℚ) : ℝ) ≤ stT259 220 := by
  have hc : ((-601467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2027545257/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-601467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c221 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-60571/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3615623/5000000) (δ := 131/10000000) (ψ := -133673/1000000) 259 223
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t221 : ((-325972627089/5000000000000 : ℚ) : ℝ) ≤ stT259 221 := by
  have hc : ((-484593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325972627089/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-484593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c222 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-151831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2154021/5000000) (δ := 13003/1000000000) (ψ := -133673/1000000) 259 223
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t222 : ((-101935996317/10000000000000 : ℚ) : ℝ) ≤ stT259 222 := by
  have hc : ((-151881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101935996317/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-151881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c223 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((847697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -698959/5000000) (δ := 13003/1000000000) (ψ := -133673/1000000) 259 223
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t223 : ((567625965903/10000000000000 : ℚ) : ℝ) ≤ stT259 223 := by
  have hc : ((847647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567625965903/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((847647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c224 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((412759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1499191/10000000) (δ := 13/1000000) (ψ := -133673/1000000) 259 223
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t224 : ((137884730151/2500000000000 : ℚ) : ℝ) ≤ stT259 224 := by
  have hc : ((206367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137884730151/2500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((206367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c225 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-181557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 876683/2000000) (δ := 13/1000000) (ψ := -133673/1000000) 259 223
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t225 : ((-121071393869/10000000000000 : ℚ) : ℝ) ≤ stT259 225 := by
  have hc : ((-181607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121071393869/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-181607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c226 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-485707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3627393/5000000) (δ := 13/500000) (ψ := -133673/1000000) 259 223
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t226 : ((-80776138703/1250000000000 : ℚ) : ℝ) ≤ stT259 226 := by
  have hc : ((-121433/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80776138703/1250000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-121433/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c227 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-618613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87413/156250) (δ := 1301/100000000) (ψ := -133673/1000000) 259 224
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t227 : ((-102655370253/2500000000000 : ℚ) : ℝ) ≤ stT259 227 := by
  have hc : ((-618663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102655370253/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-618663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c228 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((454209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2748281/10000000) (δ := 1301/100000000) (ψ := -133673/1000000) 259 224
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t228 : ((150387032147/5000000000000 : ℚ) : ℝ) ≤ stT259 228 := by
  have hc : ((454159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150387032147/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((454159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c229 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((124927/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42719/5000000) (δ := 1301/100000000) (ψ := -133673/1000000) 259 224
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t229 : ((165099760347/2500000000000 : ℚ) : ℝ) ≤ stT259 229 := by
  have hc : ((499683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165099760347/2500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((499683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c230 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((24803/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 290679/1000000) (δ := 1311/100000000) (ψ := -133673/1000000) 259 224
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t230 : ((6541016631/250000000000 : ℚ) : ℝ) ≤ stT259 230 := by
  have hc : ((198399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6541016631/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((198399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c231 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-164011/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 89311/156250) (δ := 1311/100000000) (ψ := -133673/1000000) 259 224
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t231 : ((-6744974367/156250000000 : ℚ) : ℝ) ≤ stT259 231 := by
  have hc : ((-328047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6744974367/156250000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-328047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c232 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-965473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7195119/10000000) (δ := 6543/500000000) (ψ := -133673/1000000) 259 225
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t232 : ((-633897711759/10000000000000 : ℚ) : ℝ) ≤ stT259 232 := by
  have hc : ((-965523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-633897711759/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-965523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c233 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-38413/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102539/2500000) (δ := 13117/1000000000) (ψ := -133673/1000000) 259 225
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t233 : ((-12585876303/1000000000000 : ℚ) : ℝ) ≤ stT259 233 := by
  have hc : ((-38423/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12585876303/1000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-38423/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c234 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((793143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409277/2500000) (δ := 13017/1000000000) (ψ := -133673/1000000) 259 225
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t234 : ((12961518899/250000000000 : ℚ) : ℝ) ≤ stT259 234 := by
  have hc : ((793093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12961518899/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((793093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c235 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((180121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1124091/10000000) (δ := 13017/1000000000) (ψ := -133673/1000000) 259 225
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t235 : ((14686431051/250000000000 : ℚ) : ℝ) ≤ stT259 235 := by
  have hc : ((180111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14686431051/250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((180111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c236 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((21367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387357/1000000) (δ := 6493/500000000) (ψ := -133673/1000000) 259 225
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t236 : ((216815207/156250000000 : ℚ) : ℝ) ≤ stT259 236 := by
  have hc : ((21317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216815207/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((21317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c237 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-879/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3305697/5000000) (δ := 6543/500000000) (ψ := -133673/1000000) 259 225
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t237 : ((-1142009017/20000000000 : ℚ) : ℝ) ≤ stT259 237 := by
  have hc : ((-17581/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1142009017/20000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-17581/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c238 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-828997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -637027/1000000) (δ := 407/31250000) (ψ := -133673/1000000) 259 226
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t238 : ((-134347895397/2500000000000 : ℚ) : ℝ) ≤ stT259 238 := by
  have hc : ((-829047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134347895397/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-829047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c239 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((27109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3655367/10000000) (δ := 3281/250000000) (ψ := -133673/1000000) 259 226
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t239 : ((17527262639/2500000000000 : ℚ) : ℝ) ≤ stT259 239 := by
  have hc : ((54193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17527262639/2500000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((54193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c240 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((464199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -237949/2500000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 226
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t240 : ((149811462239/2500000000000 : ℚ) : ℝ) ≤ stT259 240 := by
  have hc : ((232087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149811462239/2500000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((232087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c241 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((383641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1740509/10000000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 226
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t241 : ((482633883/9765625000 : ℚ) : ℝ) ≤ stT259 241 := by
  have hc : ((11988/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482633883/9765625000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((11988/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c242 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-98293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4421677/10000000) (δ := 12979/1000000000) (ψ := -133673/1000000) 259 226
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t242 : ((-1264025367/100000000000 : ℚ) : ℝ) ≤ stT259 242 := by
  have hc : ((-49159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1264025367/100000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-49159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c243 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-476941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7091773/10000000) (δ := 407/31250000) (ψ := -133673/1000000) 259 226
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t243 : ((-152987082983/2500000000000 : ℚ) : ℝ) ≤ stT259 243 := by
  have hc : ((-238483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152987082983/2500000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-238483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c244 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-725677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5957037/10000000) (δ := 13131/1000000000) (ψ := -133673/1000000) 259 227
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t244 : ((-92919907899/2000000000000 : ℚ) : ℝ) ≤ stT259 244 := by
  have hc : ((-725727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92919907899/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-725727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c245 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((122383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661759/2000000) (δ := 6493/250000000) (ψ := -133673/1000000) 259 227
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t245 : ((9771448701/625000000000 : ℚ) : ℝ) ≤ stT259 245 := by
  have hc : ((61179/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9771448701/625000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((61179/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c246 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((241041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671301/10000000) (δ := 817/62500000) (ψ := -133673/1000000) 259 227
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t246 : ((38418496729/625000000000 : ℚ) : ℝ) ≤ stT259 246 := by
  have hc : ((482057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38418496729/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((482057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c247 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((709371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1955477/10000000) (δ := 817/62500000) (ψ := -133673/1000000) 259 227
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t247 : ((112832400791/2500000000000 : ℚ) : ℝ) ≤ stT259 247 := by
  have hc : ((709321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112832400791/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((709321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c248 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-25501/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1142909/2500000) (δ := 817/62500000) (ψ := -133673/1000000) 259 227
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t248 : ((-8098167753/500000000000 : ℚ) : ℝ) ≤ stT259 248 := by
  have hc : ((-12753/50000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8098167753/500000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-12753/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c249 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-192717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7177241/10000000) (δ := 3243/250000000) (ψ := -133673/1000000) 259 227
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t249 : ((-4885436723/80000000000 : ℚ) : ℝ) ≤ stT259 249 := by
  have hc : ((-192727/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4885436723/80000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-192727/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c250 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-719717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5935477/10000000) (δ := 6569/500000000) (ψ := -133673/1000000) 259 228
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t250 : ((-56902619719/1250000000000 : ℚ) : ℝ) ≤ stT259 250 := by
  have hc : ((-719767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56902619719/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-719767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c251 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((228497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3350657/10000000) (δ := 6569/500000000) (ψ := -133673/1000000) 259 228
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t251 : ((72097187859/5000000000000 : ℚ) : ℝ) ≤ stT259 251 := by
  have hc : ((228447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72097187859/5000000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((228447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c252 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((190439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -776133/10000000) (δ := 2613/200000000) (ψ := -133673/1000000) 259 228
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t252 : ((5997942213/100000000000 : ℚ) : ℝ) ≤ stT259 252 := by
  have hc : ((190429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5997942213/100000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((190429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c253 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((754903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 894113/5000000) (δ := 2613/200000000) (ψ := -133673/1000000) 259 228
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t253 : ((237285775991/5000000000000 : ℚ) : ℝ) ≤ stT259 253 := by
  have hc : ((754853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).1
  have hw2 : ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((314347/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237285775991/5000000000000 : ℚ) : ℝ)
      = ((314347/5000000 : ℚ) : ℝ) * ((754853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c254 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-165433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085621/2500000) (δ := 2613/200000000) (ψ := -133673/1000000) 259 228
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t254 : ((-405598833/39062500000 : ℚ) : ℝ) ≤ stT259 254 := by
  have hc : ((-165483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-405598833/39062500000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-165483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c255 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-926079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3443353/5000000) (δ := 2593/200000000) (ψ := -133673/1000000) 259 228
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t255 : ((-23198605321/400000000000 : ℚ) : ℝ) ≤ stT259 255 := by
  have hc : ((-926129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23198605321/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-926129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c256 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-161983/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6287007/10000000) (δ := 12957/1000000000) (ψ := -133673/1000000) 259 229
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t256 : ((-101245786993/2000000000000 : ℚ) : ℝ) ≤ stT259 256 := by
  have hc : ((-161993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101245786993/2000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-161993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c257 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((16421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3762663/10000000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 229
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t257 : ((10235326947/2500000000000 : ℚ) : ℝ) ≤ stT259 257 := by
  have hc : ((32817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10235326947/2500000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((32817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c258 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((877947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1248097/10000000) (δ := 6523/500000000) (ψ := -133673/1000000) 259 229
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t258 : ((136638522771/2500000000000 : ℚ) : ℝ) ≤ stT259 258 := by
  have hc : ((877897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136638522771/2500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((877897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c259 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((219071/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1256757/10000000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 229
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t259 : ((272232322173/5000000000000 : ℚ) : ℝ) ≤ stT259 259 := by
  have hc : ((438117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272232322173/5000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((438117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c260 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((34977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3751963/10000000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 229
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t260 : ((2709535837/625000000000 : ℚ) : ℝ) ≤ stT259 260 := by
  have hc : ((4369/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2709535837/625000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((4369/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c261 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-399081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3118793/5000000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 229
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t261 : ((-24704062741/500000000000 : ℚ) : ℝ) ≤ stT259 261 := by
  have hc : ((-199553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24704062741/500000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-199553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c262 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-235363/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6994273/10000000) (δ := 38853/1000000000) (ψ := -133673/1000000) 259 230
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t262 : ((-290831380053/5000000000000 : ℚ) : ℝ) ≤ stT259 262 := by
  have hc : ((-470751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290831380053/5000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-470751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c263 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-59487/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2263811/5000000) (δ := 261/20000000) (ψ := -133673/1000000) 259 230
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t263 : ((-73377996373/5000000000000 : ℚ) : ℝ) ≤ stT259 263 := by
  have hc : ((-118999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73377996373/5000000000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-118999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c264 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((676263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414059/2000000) (δ := 781/20000000) (ψ := -133673/1000000) 259 230
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t264 : ((416180024341/10000000000000 : ℚ) : ℝ) ≤ stT259 264 := by
  have hc : ((676213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416180024341/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((676213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c265 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((988609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 377709/10000000) (δ := 13053/1000000000) (ψ := -133673/1000000) 259 230
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t265 : ((121453370181/2000000000000 : ℚ) : ℝ) ≤ stT259 265 := by
  have hc : ((988559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121453370181/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((988559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c266 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((214863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2816517/10000000) (δ := 263/20000000) (ψ := -133673/1000000) 259 230
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t266 : ((65862778241/2500000000000 : ℚ) : ℝ) ≤ stT259 266 := by
  have hc : ((107419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65862778241/2500000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((107419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c267 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-50351/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1311533/2500000) (δ := 13053/1000000000) (ψ := -133673/1000000) 259 230
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t267 : ((-7704354699/250000000000 : ℚ) : ℝ) ≤ stT259 267 := by
  have hc : ((-12589/25000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7704354699/250000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-12589/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c268 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-199439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7666681/10000000) (δ := 12953/1000000000) (ψ := -133673/1000000) 259 230
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t268 : ((-3807281961/62500000000 : ℚ) : ℝ) ≤ stT259 268 := by
  have hc : ((-199449/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3807281961/62500000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-199449/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c269 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-314823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5629733/10000000) (δ := 653/50000000) (ψ := -133673/1000000) 259 231
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t269 : ((-5998946529/156250000000 : ℚ) : ℝ) ≤ stT259 269 := by
  have hc : ((-9839/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5998946529/156250000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-9839/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c270 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((138153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40339/125000) (δ := 13043/1000000000) (ψ := -133673/1000000) 259 231
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t270 : ((262693557/15625000000 : ℚ) : ℝ) ≤ stT259 270 := by
  have hc : ((8633/31250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262693557/15625000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((8633/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c271 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((944951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -833377/10000000) (δ := 81/6250000) (ψ := -133673/1000000) 259 231
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t271 : ((17937055683/312500000000 : ℚ) : ℝ) ≤ stT259 271 := by
  have hc : ((944901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17937055683/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((944901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c272 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((813531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310299/2000000) (δ := 81/6250000) (ψ := -133673/1000000) 259 231
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t272 : ((493245256059/10000000000000 : ℚ) : ℝ) ≤ stT259 272 := by
  have hc : ((813481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493245256059/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((813481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c273 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1963813/5000000) (δ := 653/50000000) (ψ := -133673/1000000) 259 231
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t273 : ((-2874833/156250000000 : ℚ) : ℝ) ≤ stT259 273 := by
  have hc : ((-19/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2874833/156250000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-19/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c274 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-40591/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1259029/2000000) (δ := 653/50000000) (ψ := -133673/1000000) 259 231
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t274 : ((-49046934001/1000000000000 : ℚ) : ℝ) ≤ stT259 274 := by
  have hc : ((-81187/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49046934001/1000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-81187/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c275 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-949243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7054041/10000000) (δ := 3259/250000000) (ψ := -133673/1000000) 259 232
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t275 : ((-572445512739/10000000000000 : ℚ) : ℝ) ≤ stT259 275 := by
  have hc : ((-949293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-572445512739/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-949293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c276 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-305727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -940749/2000000) (δ := 13067/1000000000) (ψ := -133673/1000000) 259 232
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t276 : ((-18405634961/1000000000000 : ℚ) : ℝ) ≤ stT259 276 := by
  have hc : ((-305777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18405634961/1000000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-305777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c277 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((585927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -590483/2500000) (δ := 12967/1000000000) (ψ := -133673/1000000) 259 232
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t277 : ((352018922557/10000000000000 : ℚ) : ℝ) ≤ stT259 277 := by
  have hc : ((585877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((352018922557/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((585877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c278 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((199987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28601/10000000) (δ := 12967/1000000000) (ψ := -133673/1000000) 259 232
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t278 : ((1499227569/25000000000 : ℚ) : ℝ) ≤ stT259 278 := by
  have hc : ((199977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1499227569/25000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((199977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c279 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((606993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287039/1250000) (δ := 821/62500000) (ψ := -133673/1000000) 259 232
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t279 : ((90841765753/2500000000000 : ℚ) : ℝ) ≤ stT259 279 := by
  have hc : ((606943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90841765753/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((606943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c280 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-135487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4613003/10000000) (δ := 13067/1000000000) (ψ := -133673/1000000) 259 232
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t280 : ((-2024600097/125000000000 : ℚ) : ℝ) ≤ stT259 280 := by
  have hc : ((-16939/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2024600097/125000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-16939/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c281 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-465609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 346067/500000) (δ := 3259/250000000) (ψ := -133673/1000000) 259 232
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t281 : ((-2777739627/50000000000 : ℚ) : ℝ) ≤ stT259 281 := by
  have hc : ((-232817/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2777739627/50000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-232817/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c282 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-854081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1621611/2500000) (δ := 6487/500000000) (ψ := -133673/1000000) 259 233
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t282 : ((-127157044363/2500000000000 : ℚ) : ℝ) ≤ stT259 282 := by
  have hc : ((-854131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127157044363/2500000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-854131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c283 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-106769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -524303/1250000) (δ := 13129/1000000000) (ψ := -133673/1000000) 259 233
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t283 : ((-63497379541/10000000000000 : ℚ) : ℝ) ≤ stT259 283 := by
  have hc : ((-106819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63497379541/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-106819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c284 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((144391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59701/312500) (δ := 6487/500000000) (ψ := -133673/1000000) 259 233
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t284 : ((8567424159/200000000000 : ℚ) : ℝ) ≤ stT259 284 := by
  have hc : ((144381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8567424159/200000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((144381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c285 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((494667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182733/5000000) (δ := 6537/500000000) (ψ := -133673/1000000) 259 233
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t285 : ((36625024927/625000000000 : ℚ) : ℝ) ≤ stT259 285 := by
  have hc : ((247321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36625024927/625000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((247321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c286 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((494631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329183/1250000) (δ := 6487/500000000) (ψ := -133673/1000000) 259 233
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t286 : ((18278230017/625000000000 : ℚ) : ℝ) ≤ stT259 286 := by
  have hc : ((494581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18278230017/625000000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((494581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c287 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-94261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2446749/5000000) (δ := 6487/500000000) (ψ := -133673/1000000) 259 233
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t287 : ((-55647950127/2500000000000 : ℚ) : ℝ) ≤ stT259 287 := by
  have hc : ((-188547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55647950127/2500000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-188547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c288 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-960127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223301/312500) (δ := 13129/1000000000) (ψ := -133673/1000000) 259 233
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t288 : ((-70723757289/1250000000000 : ℚ) : ℝ) ≤ stT259 288 := by
  have hc : ((-960177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70723757289/1250000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-960177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c289 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-204279/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3158983/5000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 234
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t289 : ((-60085807397/1250000000000 : ℚ) : ℝ) ≤ stT259 289 := by
  have hc : ((-408583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60085807397/1250000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-408583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c290 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-61687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4081307/10000000) (δ := 6491/500000000) (ψ := -133673/1000000) 259 234
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t290 : ((-36253262877/10000000000000 : ℚ) : ℝ) ≤ stT259 290 := by
  have hc : ((-61737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36253262877/10000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-61737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c291 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((92227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -926209/5000000) (δ := 13021/1000000000) (ψ := -133673/1000000) 259 234
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t291 : ((21624290343/500000000000 : ℚ) : ℝ) ≤ stT259 291 := by
  have hc : ((368883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21624290343/500000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((368883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c292 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((989133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2882/78125) (δ := 6541/500000000) (ψ := -133673/1000000) 259 234
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t292 : ((115763263403/2000000000000 : ℚ) : ℝ) ≤ stT259 292 := by
  have hc : ((989083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115763263403/2000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((989083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c293 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((512221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2582569/10000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 234
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t293 : ((149606685613/5000000000000 : ℚ) : ℝ) ≤ stT259 293 := by
  have hc : ((512171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149606685613/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((512171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c294 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-168943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2394333/5000000) (δ := 6491/500000000) (ψ := -133673/1000000) 259 234
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t294 : ((-3079505163/156250000000 : ℚ) : ℝ) ≤ stT259 294 := by
  have hc : ((-21121/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3079505163/156250000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-21121/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c295 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-940511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6987317/10000000) (δ := 6491/500000000) (ψ := -133673/1000000) 259 234
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t295 : ((-547616247103/10000000000000 : ℚ) : ℝ) ≤ stT259 295 := by
  have hc : ((-940561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547616247103/10000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-940561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c296 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-8629/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3264721/5000000) (δ := 6557/500000000) (ψ := -133673/1000000) 259 235
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t296 : ((-10031603901/200000000000 : ℚ) : ℝ) ≤ stT259 296 := by
  have hc : ((-17259/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10031603901/200000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-17259/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c297 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-166669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2172809/5000000) (δ := 13089/1000000000) (ψ := -133673/1000000) 259 235
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t297 : ((-96740200221/10000000000000 : ℚ) : ℝ) ≤ stT259 297 := by
  have hc : ((-166719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96740200221/10000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-166719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c298 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((129321/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2169177/10000000) (δ := 6557/500000000) (ψ := -133673/1000000) 259 235
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t298 : ((18726948331/500000000000 : ℚ) : ℝ) ≤ stT259 298 := by
  have hc : ((129311/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18726948331/500000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((129311/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c299 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13/10000000) (δ := 6507/500000000) (ψ := -133673/1000000) 259 235
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t299 : ((5782850843/100000000000 : ℚ) : ℝ) ≤ stT259 299 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5782850843/100000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c300 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((648807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2161951/10000000) (δ := 12989/1000000000) (ψ := -133673/1000000) 259 235
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t300 : ((7491197079/200000000000 : ℚ) : ℝ) ≤ stT259 300 := by
  have hc : ((648757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7491197079/200000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((648757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c301 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-77627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4316701/10000000) (δ := 6557/500000000) (ψ := -133673/1000000) 259 235
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t301 : ((-11189478483/1250000000000 : ℚ) : ℝ) ≤ stT259 301 := by
  have hc : ((-19413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11189478483/1250000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-19413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c302 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-424723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6464329/10000000) (δ := 6557/500000000) (ψ := -133673/1000000) 259 235
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t302 : ((-15275955633/312500000000 : ℚ) : ℝ) ≤ stT259 302 := by
  have hc : ((-106187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15275955633/312500000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-106187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c303 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-238809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -887891/1250000) (δ := 1637/125000000) (ψ := -133673/1000000) 259 236
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t303 : ((-54879747771/1000000000000 : ℚ) : ℝ) ≤ stT259 303 := by
  have hc : ((-477643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54879747771/1000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-477643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c304 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-405089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4969681/10000000) (δ := 13107/1000000000) (ψ := -133673/1000000) 259 236
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t304 : ((-11618171103/500000000000 : ℚ) : ℝ) ≤ stT259 304 := by
  have hc : ((-405139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11618171103/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-405139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c305 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((420031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2843291/10000000) (δ := 13107/1000000000) (ψ := -133673/1000000) 259 236
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t305 : ((120240140319/5000000000000 : ℚ) : ℝ) ≤ stT259 305 := by
  have hc : ((419981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120240140319/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((419981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c306 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((191677/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180941/2500000) (δ := 3249/250000000) (ψ := -133673/1000000) 259 236
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t306 : ((109568548887/2000000000000 : ℚ) : ℝ) ≤ stT259 306 := by
  have hc : ((191667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109568548887/2000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((191667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c307 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((849633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1388769/10000000) (δ := 13107/1000000000) (ψ := -133673/1000000) 259 236
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t307 : ((48488250559/1000000000000 : ℚ) : ℝ) ≤ stT259 307 := by
  have hc : ((849583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48488250559/1000000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((849583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c308 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((172159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3494439/10000000) (δ := 13107/1000000000) (ψ := -133673/1000000) 259 236
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t308 : ((49034026209/5000000000000 : ℚ) : ℝ) ≤ stT259 308 := by
  have hc : ((172109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49034026209/5000000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((172109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c309 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-618261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5593311/10000000) (δ := 1637/125000000) (ψ := -133673/1000000) 259 236
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t309 : ((-351745379991/10000000000000 : ℚ) : ℝ) ≤ stT259 309 := by
  have hc : ((-618311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351745379991/10000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-618311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c310 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-997727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7685383/10000000) (δ := 13007/1000000000) (ψ := -133673/1000000) 259 236
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t310 : ((-283349710237/5000000000000 : ℚ) : ℝ) ≤ stT259 310 := by
  have hc : ((-997777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283349710237/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-997777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c311 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-720189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5937177/10000000) (δ := 13/1000000) (ψ := -133673/1000000) 259 237
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t311 : ((-51051260559/1250000000000 : ℚ) : ℝ) ≤ stT259 311 := by
  have hc : ((-720239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51051260559/1250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-720239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c312 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((6841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -964643/2500000) (δ := 13103/1000000000) (ψ := -133673/1000000) 259 237
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t312 : ((3865873333/2500000000000 : ℚ) : ℝ) ≤ stT259 312 := by
  have hc : ((13657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3865873333/2500000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((13657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c313 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((755337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -446643/2500000) (δ := 13103/1000000000) (ψ := -133673/1000000) 259 237
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t313 : ((426913136871/10000000000000 : ℚ) : ℝ) ≤ stT259 313 := by
  have hc : ((755287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426913136871/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((755287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c314 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((993787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278823/10000000) (δ := 13/1000000) (ψ := -133673/1000000) 259 237
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t314 : ((140199397171/2500000000000 : ℚ) : ℝ) ≤ stT259 314 := by
  have hc : ((993737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140199397171/2500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((993737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c315 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((593761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2337679/10000000) (δ := 13003/1000000000) (ψ := -133673/1000000) 259 237
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t315 : ((83629537749/2500000000000 : ℚ) : ℝ) ≤ stT259 315 := by
  have hc : ((593711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83629537749/2500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((593711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c316 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-36829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 877999/2000000) (δ := 13003/1000000000) (ψ := -133673/1000000) 259 237
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t316 : ((-1295222401/125000000000 : ℚ) : ℝ) ≤ stT259 316 := by
  have hc : ((-36839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1295222401/125000000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-36839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c317 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-843363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6435771/10000000) (δ := 13/1000000) (ψ := -133673/1000000) 259 237
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t317 : ((-59213496491/1250000000000 : ℚ) : ℝ) ≤ stT259 317 := by
  have hc : ((-843413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59213496491/1250000000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-843413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c318 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-242323/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3616413/5000000) (δ := 1301/100000000) (ψ := -133673/1000000) 259 238
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t318 : ((-271790410683/5000000000000 : ℚ) : ℝ) ≤ stT259 318 := by
  have hc : ((-484671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271790410683/5000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-484671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c319 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-243707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2599903/5000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 238
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t319 : ((-34115960169/1250000000000 : ℚ) : ℝ) ≤ stT259 319 := by
  have hc : ((-60933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34115960169/1250000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-60933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c320 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((148473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158663/500000) (δ := 1301/100000000) (ψ := -133673/1000000) 259 238
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t320 : ((324159403/19531250000 : ℚ) : ℝ) ≤ stT259 320 := by
  have hc : ((4639/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).1
  have hw2 : ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69877/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324159403/19531250000 : ℚ) : ℝ)
      = ((69877/1250000 : ℚ) : ℝ) * ((4639/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c321 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((895531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1152931/10000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 238
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t321 : ((99961648549/2000000000000 : ℚ) : ℝ) ≤ stT259 321 := by
  have hc : ((895481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99961648549/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((895481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c322 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((941271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 861053/10000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 238
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t322 : ((262260878219/5000000000000 : ℚ) : ℝ) ≤ stT259 322 := by
  have hc : ((941221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262260878219/5000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((941221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c323 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((205371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2868821/10000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 238
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t323 : ((28564347311/1250000000000 : ℚ) : ℝ) ≤ stT259 323 := by
  have hc : ((102673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28564347311/1250000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((102673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c324 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-368461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4870373/10000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 238
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t324 : ((-51182124279/2500000000000 : ℚ) : ℝ) ≤ stT259 324 := by
  have hc : ((-368511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).2
  have h0 : (0:ℝ) ≤ ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51182124279/2500000000000 : ℚ) : ℝ)
      = ((138889/2500000 : ℚ) : ℝ) * ((-368511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c325 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-461439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6865709/10000000) (δ := 13093/1000000000) (ψ := -133673/1000000) 259 238
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t325 : ((-31996817783/625000000000 : ℚ) : ℝ) ≤ stT259 325 := by
  have hc : ((-57683/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31996817783/625000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-57683/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c326 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-920909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1713251/2500000) (δ := 13117/1000000000) (ψ := -133673/1000000) 259 239
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t326 : ((-510072221191/10000000000000 : ℚ) : ℝ) ≤ stT259 326 := by
  have hc : ((-920959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-510072221191/10000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-920959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c327 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-368263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4869841/10000000) (δ := 13117/1000000000) (ψ := -133673/1000000) 259 239
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t327 : ((-101838912813/5000000000000 : ℚ) : ℝ) ≤ stT259 327 := by
  have hc : ((-368313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101838912813/5000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-368313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c328 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((80403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28927/100000) (δ := 13017/1000000000) (ψ := -133673/1000000) 259 239
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t328 : ((44389557701/2000000000000 : ℚ) : ℝ) ≤ stT259 328 := by
  have hc : ((80393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44389557701/2000000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((80393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c329 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((233203/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184329/2000000) (δ := 13117/1000000000) (ψ := -133673/1000000) 259 239
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t329 : ((257123773777/5000000000000 : ℚ) : ℝ) ≤ stT259 329 := by
  have hc : ((466381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257123773777/5000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((466381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c330 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((457077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260863/2500000) (δ := 6543/500000000) (ψ := -133673/1000000) 259 239
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t330 : ((62899610503/1250000000000 : ℚ) : ℝ) ≤ stT259 330 := by
  have hc : ((114263/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62899610503/1250000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((114263/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c331 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((361391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3002593/10000000) (δ := 6493/500000000) (ψ := -133673/1000000) 259 239
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t331 : ((198610719309/10000000000000 : ℚ) : ℝ) ≤ stT259 331 := by
  have hc : ((361341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198610719309/10000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((361341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c332 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-200011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2477921/5000000) (δ := 13117/1000000000) (ψ := -133673/1000000) 259 239
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t332 : ((-13723019699/625000000000 : ℚ) : ℝ) ≤ stT259 332 := by
  have hc : ((-50009/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13723019699/625000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-50009/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c333 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-232137/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3451599/5000000) (δ := 13017/1000000000) (ψ := -133673/1000000) 259 239
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t333 : ((-254434459103/5000000000000 : ℚ) : ℝ) ≤ stT259 333 := by
  have hc : ((-464299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254434459103/5000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-464299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c334 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-14414/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6863237/10000000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 240
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t334 : ((-31549689381/625000000000 : ℚ) : ℝ) ≤ stT259 334 := by
  have hc : ((-461273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31549689381/625000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-461273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c335 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-77919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4927471/10000000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 240
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t335 : ((-42577210511/2000000000000 : ℚ) : ℝ) ≤ stT259 335 := by
  have hc : ((-77929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42577210511/2000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-77929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c336 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((181639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -749383/2500000) (δ := 521/40000000) (ψ := -133673/1000000) 259 240
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t336 : ((6192401751/312500000000 : ℚ) : ℝ) ≤ stT259 336 := by
  have hc : ((90807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6192401751/312500000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((90807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c337 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((3637/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268323/2500000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 240
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t337 : ((619090191/12500000000 : ℚ) : ℝ) ≤ stT259 337 := by
  have hc : ((2273/2500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((619090191/12500000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((2273/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c338 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((188679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 422593/5000000) (δ := 6489/500000000) (ψ := -133673/1000000) 259 240
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t338 : ((12827793979/250000000000 : ℚ) : ℝ) ≤ stT259 338 := by
  have hc : ((188669/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12827793979/250000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((188669/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c339 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((112677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 551619/2000000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 240
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t339 : ((195810901/8000000000 : ℚ) : ℝ) ≤ stT259 339 := by
  have hc : ((225329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195810901/8000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((225329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c340 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-72763/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4665307/10000000) (δ := 21/1600000) (ψ := -133673/1000000) 259 240
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t340 : ((-78936237177/5000000000000 : ℚ) : ℝ) ≤ stT259 340 := by
  have hc : ((-145551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78936237177/5000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-145551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c341 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-217593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1313377/2000000) (δ := 21/1600000) (ψ := -133673/1000000) 259 240
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t341 : ((-235680248041/5000000000000 : ℚ) : ℝ) ≤ stT259 341 := by
  have hc : ((-435211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235680248041/5000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-435211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c342 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-485239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1811251/2500000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 241
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t342 : ((-16400073131/312500000000 : ℚ) : ℝ) ≤ stT259 342 := by
  have hc : ((-30329/31250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16400073131/312500000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-30329/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c343 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-135119/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5354499/10000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 241
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t343 : ((-2918570137/100000000000 : ℚ) : ℝ) ≤ stT259 343 := by
  have hc : ((-270263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2918570137/100000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-270263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c344 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((90989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3469497/10000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 241
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t344 : ((12261105783/1250000000000 : ℚ) : ℝ) ≤ stT259 344 := by
  have hc : ((22741/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12261105783/1250000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((22741/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c345 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((402247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794967/5000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 241
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t345 : ((108274341291/2500000000000 : ℚ) : ℝ) ≤ stT259 345 := by
  have hc : ((201111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108274341291/2500000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((201111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c346 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((993549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142063/5000000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 241
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t346 : ((534108042897/10000000000000 : ℚ) : ℝ) ≤ stT259 346 := by
  have hc : ((993499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((534108042897/10000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((993499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c347 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((130317/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2152811/10000000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 241
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t347 : ((17488111549/500000000000 : ℚ) : ℝ) ≤ stT259 347 := by
  have hc : ((130307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17488111549/500000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((130307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c348 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-7129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4016121/10000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 241
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t348 : ((-3826910923/2000000000000 : ℚ) : ℝ) ≤ stT259 348 := by
  have hc : ((-7139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3826910923/2000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-7139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c349 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-702463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5874123/10000000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 241
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t349 : ((-47005847343/1250000000000 : ℚ) : ℝ) ≤ stT259 349 := by
  have hc : ((-702513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47005847343/1250000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-702513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c350 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-199741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30907/40000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 241
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t350 : ((-106771503773/2000000000000 : ℚ) : ℝ) ≤ stT259 350 := by
  have hc : ((-199751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106771503773/2000000000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-199751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c351 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-772479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6133831/10000000) (δ := 13139/1000000000) (ψ := -133673/1000000) 259 242
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t351 : ((-412345851569/10000000000000 : ℚ) : ℝ) ≤ stT259 351 := by
  have hc : ((-772529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-412345851569/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-772529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c352 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-14539/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4291759/10000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 242
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t352 : ((-242249409/31250000000 : ℚ) : ℝ) ≤ stT259 352 := by
  have hc : ((-909/6250 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242249409/31250000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-909/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c353 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((111081/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1227433/5000000) (δ := 3241/250000000) (ψ := -133673/1000000) 259 242
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t353 : ((29558547733/1000000000000 : ℚ) : ℝ) ≤ stT259 353 := by
  have hc : ((111071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29558547733/1000000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((111071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c354 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((193819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -623153/10000000) (δ := 13039/1000000000) (ψ := -133673/1000000) 259 242
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t354 : ((51504160323/1000000000000 : ℚ) : ℝ) ≤ stT259 354 := by
  have hc : ((193809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51504160323/1000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((193809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c355 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((443191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 240663/2000000) (δ := 13039/1000000000) (ψ := -133673/1000000) 259 242
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t355 : ((14700480969/312500000000 : ℚ) : ℝ) ≤ stT259 355 := by
  have hc : ((221583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14700480969/312500000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((221583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c356 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((2207/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756183/2500000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 242
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t356 : ((9356319693/500000000000 : ℚ) : ℝ) ≤ stT259 356 := by
  have hc : ((35307/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9356319693/500000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((35307/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c357 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-178751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484097/1000000) (δ := 13039/1000000000) (ψ := -133673/1000000) 259 242
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t357 : ((-11827306179/625000000000 : ℚ) : ℝ) ≤ stT259 357 := by
  have hc : ((-22347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11827306179/625000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-22347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c358 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-443329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6652157/10000000) (δ := 13039/1000000000) (ψ := -133673/1000000) 259 242
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t358 : ((-117160063009/2500000000000 : ℚ) : ℝ) ≤ stT259 358 := by
  have hc : ((-221677/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117160063009/2500000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-221677/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c359 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-970927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -724967/1000000) (δ := 12957/1000000000) (ψ := -133673/1000000) 259 243
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t359 : ((-25623112053/500000000000 : ℚ) : ℝ) ≤ stT259 359 := by
  have hc : ((-970977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25623112053/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-970977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c360 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-571729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5448519/10000000) (δ := 6523/500000000) (ψ := -133673/1000000) 259 243
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t360 : ((-301354406613/10000000000000 : ℚ) : ℝ) ≤ stT259 360 := by
  have hc : ((-571779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301354406613/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-571779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c361 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((13701/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3652419/10000000) (δ := 12957/1000000000) (ψ := -133673/1000000) 259 243
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t361 : ((5766201877/1000000000000 : ℚ) : ℝ) ≤ stT259 361 := by
  have hc : ((54779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5766201877/1000000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((54779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c362 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((73543/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46531/250000) (δ := 13057/1000000000) (ψ := -133673/1000000) 259 243
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t362 : ((4831336293/125000000000 : ℚ) : ℝ) ≤ stT259 362 := by
  have hc : ((36769/50000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4831336293/125000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((36769/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c363 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((999549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37523/5000000) (δ := 6523/500000000) (ψ := -133673/1000000) 259 243
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t363 : ((524600043637/10000000000000 : ℚ) : ℝ) ≤ stT259 363 := by
  have hc : ((999499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524600043637/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((999499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c364 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((194001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 853113/5000000) (δ := 13057/1000000000) (ψ := -133673/1000000) 259 243
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t364 : ((101677520367/2500000000000 : ℚ) : ℝ) ≤ stT259 364 := by
  have hc : ((387977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101677520367/2500000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((387977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c365 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((35361/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3482643/10000000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 243
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t365 : ((18503526473/2000000000000 : ℚ) : ℝ) ≤ stT259 365 := by
  have hc : ((35351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18503526473/2000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((35351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c366 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-506297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5254203/10000000) (δ := 6573/500000000) (ψ := -133673/1000000) 259 243
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t366 : ((-264672134023/10000000000000 : ℚ) : ℝ) ≤ stT259 366 := by
  have hc : ((-506347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264672134023/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-506347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c367 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-944991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3510453/5000000) (δ := 13057/1000000000) (ψ := -133673/1000000) 259 243
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t367 : ((-123326905459/2500000000000 : ℚ) : ℝ) ≤ stT259 367 := by
  have hc : ((-945041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123326905459/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-945041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c368 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-931771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1385029/2000000) (δ := 261/20000000) (ψ := -133673/1000000) 259 244
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t368 : ((-485746173627/10000000000000 : ℚ) : ℝ) ≤ stT259 368 := by
  have hc : ((-931821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485746173627/10000000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-931821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c369 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-19051/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -646003/1250000) (δ := 12953/1000000000) (ψ := -133673/1000000) 259 244
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t369 : ((-495930537/20000000000 : ℚ) : ℝ) ≤ stT259 369 := by
  have hc : ((-19053/40000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-495930537/20000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-19053/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c370 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((203121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341563/1000000) (δ := 12953/1000000000) (ψ := -133673/1000000) 259 244
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t370 : ((844572289/80000000000 : ℚ) : ℝ) ≤ stT259 370 := by
  have hc : ((203071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((844572289/80000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((203071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c371 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((15711/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417007/2500000) (δ := 263/20000000) (ψ := -133673/1000000) 259 244
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t371 : ((407811177/10000000000 : ℚ) : ℝ) ≤ stT259 371 := by
  have hc : ((1571/2000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407811177/10000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((1571/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c372 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((999551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74913/10000000) (δ := 12953/1000000000) (ψ := -133673/1000000) 259 244
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t372 : ((20728651239/400000000000 : ℚ) : ℝ) ≤ stT259 372 := by
  have hc : ((999501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20728651239/400000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((999501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c373 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((187079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1813191/10000000) (δ := 263/20000000) (ψ := -133673/1000000) 259 244
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t373 : ((9685929237/250000000000 : ℚ) : ℝ) ≤ stT259 373 := by
  have hc : ((374133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9685929237/250000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((374133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c374 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((151513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3546743/10000000) (δ := 261/20000000) (ψ := -133673/1000000) 259 244
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t374 : ((78319548281/10000000000000 : ℚ) : ℝ) ≤ stT259 374 := by
  have hc : ((151463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78319548281/10000000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((151463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c375 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-256857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2637881/5000000) (δ := 263/20000000) (ψ := -133673/1000000) 259 244
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t375 : ((-33163337759/1250000000000 : ℚ) : ℝ) ≤ stT259 375 := by
  have hc : ((-128441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33163337759/1250000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-128441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c376 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-471119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175003/250000) (δ := 13053/1000000000) (ψ := -133673/1000000) 259 244
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t376 : ((-30371767923/625000000000 : ℚ) : ℝ) ≤ stT259 376 := by
  have hc : ((-58893/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30371767923/625000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-58893/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c377 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-188123/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1747021/2500000) (δ := 13143/1000000000) (ψ := -133673/1000000) 259 245
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t377 : ((-96893574591/2000000000000 : ℚ) : ℝ) ≤ stT259 377 := by
  have hc : ((-188133/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96893574591/2000000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-188133/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c378 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-512717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -659107/1250000) (δ := 81/6250000) (ψ := -133673/1000000) 259 245
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t378 : ((-52747828523/2000000000000 : ℚ) : ℝ) ≤ stT259 378 := by
  have hc : ((-512767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).2
  have h0 : (0:ℝ) ≤ ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52747828523/2000000000000 : ℚ) : ℝ)
      = ((102869/2000000 : ℚ) : ℝ) * ((-512767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c379 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((909/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222631/625000) (δ := 653/50000000) (ψ := -133673/1000000) 259 245
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t379 : ((1493635087/200000000000 : ℚ) : ℝ) ≤ stT259 379 := by
  have hc : ((14539/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1493635087/200000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((14539/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c380 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((368433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -927967/5000000) (δ := 13043/1000000000) (ψ := -133673/1000000) 259 245
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t380 : ((23623656439/625000000000 : ℚ) : ℝ) ≤ stT259 380 := by
  have hc : ((46051/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23623656439/625000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((46051/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c381 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((998097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154239/10000000) (δ := 81/6250000) (ψ := -133673/1000000) 259 245
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t381 : ((102262889761/2000000000000 : ℚ) : ℝ) ≤ stT259 381 := by
  have hc : ((998047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102262889761/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((998047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c382 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((81549/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543053/10000000) (δ := 653/50000000) (ψ := -133673/1000000) 259 245
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t382 : ((1303796823/31250000000 : ℚ) : ℝ) ≤ stT259 382 := by
  have hc : ((10193/12500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1303796823/31250000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((10193/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c383 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((272963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 808953/2500000) (δ := 81/6250000) (ψ := -133673/1000000) 259 245
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t383 : ((136183587/9765625000 : ℚ) : ℝ) ≤ stT259 383 := by
  have hc : ((272913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136183587/9765625000 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((272913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c384 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-194201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4924233/10000000) (δ := 81/6250000) (ψ := -133673/1000000) 259 245
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t384 : ((-49557832143/2500000000000 : ℚ) : ℝ) ≤ stT259 384 := by
  have hc : ((-97113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49557832143/2500000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-97113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c385 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-549/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6608251/10000000) (δ := 81/6250000) (ψ := -133673/1000000) 259 245
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t385 : ((-559625357/12500000000 : ℚ) : ℝ) ≤ stT259 385 := by
  have hc : ((-17569/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-559625357/12500000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-17569/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c386 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-984977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7420097/10000000) (δ := 3267/250000000) (ψ := -133673/1000000) 259 246
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t386 : ((-501365937649/10000000000000 : ℚ) : ℝ) ≤ stT259 386 := by
  have hc : ((-985027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-501365937649/10000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-985027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c387 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-66473/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5744821/10000000) (δ := 2627/200000000) (ψ := -133673/1000000) 259 246
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t387 : ((-16896347631/500000000000 : ℚ) : ℝ) ≤ stT259 387 := by
  have hc : ((-33239/50000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16896347631/500000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-33239/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c388 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-58697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4073817/10000000) (δ := 3267/250000000) (ψ := -133673/1000000) 259 246
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t388 : ((-14912162239/5000000000000 : ℚ) : ℝ) ≤ stT259 388 := by
  have hc : ((-58747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14912162239/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-58747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c389 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((285587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150447/625000) (δ := 3267/250000000) (ψ := -133673/1000000) 259 246
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t389 : ((3619641131/125000000000 : ℚ) : ℝ) ≤ stT259 389 := by
  have hc : ((142781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3619641131/125000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((142781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c390 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((477977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744761/10000000) (δ := 2607/200000000) (ψ := -133673/1000000) 259 246
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t390 : ((945390923/19531250000 : ℚ) : ℝ) ≤ stT259 390 := by
  have hc : ((14936/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((945390923/19531250000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((14936/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c391 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((934001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 913357/10000000) (δ := 2607/200000000) (ψ := -133673/1000000) 259 246
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t391 : ((472318633671/10000000000000 : ℚ) : ℝ) ≤ stT259 391 := by
  have hc : ((933951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((472318633671/10000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((933951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c392 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((517469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1283633/5000000) (δ := 2627/200000000) (ψ := -133673/1000000) 259 246
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t392 : ((65333979711/2500000000000 : ℚ) : ℝ) ≤ stT259 392 := by
  have hc : ((517419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65333979711/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((517419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c393 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-115731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4216967/10000000) (δ := 1621/125000000) (ψ := -133673/1000000) 259 246
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t393 : ((-29201936477/5000000000000 : ℚ) : ℝ) ≤ stT259 393 := by
  have hc : ((-115781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29201936477/5000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-115781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c394 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-139827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5862459/10000000) (δ := 3267/250000000) (ψ := -133673/1000000) 259 246
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t394 : ((-70448901741/2000000000000 : ℚ) : ℝ) ≤ stT259 394 := by
  have hc : ((-139837/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70448901741/2000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-139837/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c395 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-990203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3751871/5000000) (δ := 3267/250000000) (ψ := -133673/1000000) 259 246
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t395 : ((-99650149643/2000000000000 : ℚ) : ℝ) ≤ stT259 395 := by
  have hc : ((-990253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99650149643/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-990253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c396 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-435199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3283509/5000000) (δ := 3257/250000000) (ψ := -133673/1000000) 259 247
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t396 : ((-27338541157/625000000000 : ℚ) : ℝ) ≤ stT259 396 := by
  have hc : ((-54403/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27338541157/625000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-54403/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c397 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-49001/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4934023/10000000) (δ := 3257/250000000) (ψ := -133673/1000000) 259 247
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t397 : ((-49192105347/2500000000000 : ℚ) : ℝ) ≤ stT259 397 := by
  have hc : ((-196029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49192105347/2500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-196029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c398 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((246221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1652521/5000000) (δ := 523/40000000) (ψ := -133673/1000000) 259 247
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t398 : ((61697099217/5000000000000 : ℚ) : ℝ) ≤ stT259 398 := by
  have hc : ((246171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61697099217/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((246171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c399 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((782527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -840103/5000000) (δ := 3257/250000000) (ψ := -133673/1000000) 259 247
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t399 : ((195864165301/5000000000000 : ℚ) : ℝ) ≤ stT259 399 := by
  have hc : ((782477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195864165301/5000000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((782477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c400 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((999717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59449/10000000) (δ := 1641/125000000) (ψ := -133673/1000000) 259 247
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t400 : ((999667/20000000 : ℚ) : ℝ) ≤ stT259 400 := by
  have hc : ((999667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((999667/20000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((999667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c401 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((40609/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778647/5000000) (δ := 3257/250000000) (ψ := -133673/1000000) 259 247
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t401 : ((2534738943/62500000000 : ℚ) : ℝ) ≤ stT259 401 := by
  have hc : ((81213/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2534738943/62500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((81213/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c402 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((298207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1584979/5000000) (δ := 523/40000000) (ψ := -133673/1000000) 259 247
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t402 : ((74353498189/5000000000000 : ℚ) : ℝ) ≤ stT259 402 := by
  have hc : ((298157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74353498189/5000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((298157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c403 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-334121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4778671/10000000) (δ := 1641/125000000) (ψ := -133673/1000000) 259 247
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t403 : ((-20807825657/1250000000000 : ℚ) : ℝ) ≤ stT259 403 := by
  have hc : ((-334171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20807825657/1250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-334171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c404 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-207979/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6383371/10000000) (δ := 523/40000000) (ψ := -133673/1000000) 259 247
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t404 : ((-206959446177/5000000000000 : ℚ) : ℝ) ≤ stT259 404 := by
  have hc : ((-415983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206959446177/5000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-415983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c405 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-199729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7723843/10000000) (δ := 6491/500000000) (ψ := -133673/1000000) 259 248
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t405 : ((-12406388507/250000000000 : ℚ) : ℝ) ≤ stT259 405 := by
  have hc : ((-199739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12406388507/250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-199739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c406 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-12043/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6127043/10000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t406 : ((-47817858273/1250000000000 : ℚ) : ℝ) ≤ stT259 406 := by
  have hc : ((-385401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47817858273/1250000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-385401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c407 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-481/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4534193/10000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t407 : ((-1192363051/100000000000 : ℚ) : ℝ) ≤ stT259 407 := by
  have hc : ((-4811/20000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1192363051/100000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-4811/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c408 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((382689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -736307/2500000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t408 : ((189434237647/10000000000000 : ℚ) : ℝ) ≤ stT259 408 := by
  have hc : ((382639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189434237647/10000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((382639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c409 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((171123/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -340037/2500000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t409 : ((21152475721/500000000000 : ℚ) : ℝ) ≤ stT259 409 := by
  have hc : ((171113/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21152475721/500000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((171113/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c410 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((498047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221047/10000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t410 : ((15372196063/312500000000 : ℚ) : ℝ) ≤ stT259 410 := by
  have hc : ((249011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15372196063/312500000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((249011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c411 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((376111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1798421/10000000) (δ := 13121/1000000000) (ψ := -133673/1000000) 259 248
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t411 : ((92754654309/2500000000000 : ℚ) : ℝ) ≤ stT259 411 := by
  have hc : ((188043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92754654309/2500000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((188043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c412 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((55053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3371911/10000000) (δ := 13021/1000000000) (ψ := -133673/1000000) 259 248
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t412 : ((6779118223/625000000000 : ℚ) : ℝ) ≤ stT259 412 := by
  have hc : ((110081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6779118223/625000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((110081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c413 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-394787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4941581/10000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t413 : ((-48571663229/2500000000000 : ℚ) : ℝ) ≤ stT259 413 := by
  have hc : ((-394837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48571663229/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-394837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c414 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-85843/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1301499/2000000) (δ := 6541/500000000) (ψ := -133673/1000000) 259 248
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t414 : ((-2637003747/62500000000 : ℚ) : ℝ) ≤ stT259 414 := by
  have hc : ((-10731/12500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2637003747/62500000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-10731/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c415 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-996281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -763831/1000000) (δ := 12989/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t415 : ((-489079957611/10000000000000 : ℚ) : ℝ) ≤ stT259 415 := by
  have hc : ((-996331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489079957611/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-996331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c416 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-37931/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1519993/2500000) (δ := 6507/500000000) (ψ := -133673/1000000) 259 249
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t416 : ((-37196907297/1000000000000 : ℚ) : ℝ) ≤ stT259 416 := by
  have hc : ((-75867/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37196907297/1000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-75867/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c417 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-47411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1131331/2500000) (δ := 13089/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t417 : ((-23222205963/2000000000000 : ℚ) : ℝ) ≤ stT259 417 := by
  have hc : ((-47421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23222205963/2000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-47421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c418 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((371871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92951/312500) (δ := 13089/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t418 : ((36372645683/2000000000000 : ℚ) : ℝ) ≤ stT259 418 := by
  have hc : ((371821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36372645683/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((371821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c419 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((841419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1427231/10000000) (δ := 12989/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t419 : ((411034838939/10000000000000 : ℚ) : ℝ) ≤ stT259 419 := by
  have hc : ((841369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411034838939/10000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((841369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c420 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((998919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116279/10000000) (δ := 6557/500000000) (ψ := -133673/1000000) 259 249
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t420 : ((9747962571/200000000000 : ℚ) : ℝ) ≤ stT259 420 := by
  have hc : ((998869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9747962571/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((998869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c421 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((394247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1656099/10000000) (δ := 6507/500000000) (ψ := -133673/1000000) 259 249
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t421 : ((9606598807/250000000000 : ℚ) : ℝ) ≤ stT259 421 := by
  have hc : ((197111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9606598807/250000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((197111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c422 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((289667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3192293/10000000) (δ := 12989/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t422 : ((17622904833/1250000000000 : ℚ) : ℝ) ≤ stT259 422 := by
  have hc : ((289617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17622904833/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((289617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c423 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-313733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1181199/2500000) (δ := 12989/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t423 : ((-152566628911/10000000000000 : ℚ) : ℝ) ≤ stT259 423 := by
  have hc : ((-313783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152566628911/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-313783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c424 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-401019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3126869/5000000) (δ := 13089/1000000000) (ψ := -133673/1000000) 259 249
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t424 : ((-48691052823/1250000000000 : ℚ) : ℝ) ≤ stT259 424 := by
  have hc : ((-100261/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48691052823/1250000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-100261/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c425 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-999551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7779053/10000000) (δ := 6557/500000000) (ψ := -133673/1000000) 259 249
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t425 : ((-30304903517/625000000000 : ℚ) : ℝ) ≤ stT259 425 := by
  have hc : ((-999601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30304903517/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-999601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c426 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-418579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1281431/2000000) (δ := 1637/125000000) (ψ := -133673/1000000) 259 250
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t426 : ((-25351809401/625000000000 : ℚ) : ℝ) ≤ stT259 426 := by
  have hc : ((-104651/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25351809401/625000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-104651/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c427 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-375363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2444481/5000000) (δ := 3249/250000000) (ψ := -133673/1000000) 259 250
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t427 : ((-90837557371/5000000000000 : ℚ) : ℝ) ≤ stT259 427 := by
  have hc : ((-375413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90837557371/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-375413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c428 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((219243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -674879/2000000) (δ := 13007/1000000000) (ψ := -133673/1000000) 259 250
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t428 : ((13243860253/1250000000000 : ℚ) : ℝ) ≤ stT259 428 := by
  have hc : ((219193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13243860253/1250000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((219193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c429 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((367441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1863259/10000000) (δ := 1637/125000000) (ψ := -133673/1000000) 259 250
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t429 : ((5543434827/156250000000 : ℚ) : ℝ) ≤ stT259 429 := by
  have hc : ((45927/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5543434827/156250000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((45927/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c430 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((123737/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71137/2000000) (δ := 3249/250000000) (ψ := -133673/1000000) 259 250
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t430 : ((119336328683/2500000000000 : ℚ) : ℝ) ≤ stT259 430 := by
  have hc : ((494923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).1
  have hw2 : ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((241121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119336328683/2500000000000 : ℚ) : ℝ)
      = ((241121/5000000 : ℚ) : ℝ) * ((494923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c431 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((896349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143541/1250000) (δ := 3249/250000000) (ψ := -133673/1000000) 259 250
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t431 : ((431731991217/10000000000000 : ℚ) : ℝ) ≤ stT259 431 := by
  have hc : ((896299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((431731991217/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((896299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c432 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((489253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2648909/10000000) (δ := 13007/1000000000) (ψ := -133673/1000000) 259 250
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t432 : ((1882942347/80000000000 : ℚ) : ℝ) ≤ stT259 432 := by
  have hc : ((489203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1882942347/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((489203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c433 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-17503/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4146059/10000000) (δ := 1637/125000000) (ψ := -133673/1000000) 259 250
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t433 : ((-841622241/200000000000 : ℚ) : ℝ) ≤ stT259 433 := by
  have hc : ((-17513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-841622241/200000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-17513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c434 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-316371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176241/312500) (δ := 1637/125000000) (ψ := -133673/1000000) 259 250
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t434 : ((-2373049099/78125000000 : ℚ) : ℝ) ≤ stT259 434 := by
  have hc : ((-79099/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2373049099/78125000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-79099/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c435 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-958353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7129933/10000000) (δ := 3249/250000000) (ψ := -133673/1000000) 259 250
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t435 : ((-57439966999/1250000000000 : ℚ) : ℝ) ≤ stT259 435 := by
  have hc : ((-958403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57439966999/1250000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-958403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c436 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-476909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7091241/10000000) (δ := 12999/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t436 : ((-57102592419/1250000000000 : ℚ) : ℝ) ≤ stT259 436 := by
  have hc : ((-238467/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57102592419/1250000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-238467/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c437 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-38927/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5607883/10000000) (δ := 3251/250000000) (ψ := -133673/1000000) 259 251
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t437 : ((-29796494793/1000000000000 : ℚ) : ℝ) ≤ stT259 437 := by
  have hc : ((-311441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29796494793/1000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-311441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c438 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-10031/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1031957/2500000) (δ := 13099/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t438 : ((-19183955031/5000000000000 : ℚ) : ℝ) ≤ stT259 438 := by
  have hc : ((-40149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19183955031/5000000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-40149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c439 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((122113/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -662801/2500000) (δ := 12999/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t439 : ((116550543873/5000000000000 : ℚ) : ℝ) ≤ stT259 439 := by
  have hc : ((244201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116550543873/5000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((244201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c440 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((445517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1177947/10000000) (δ := 3251/250000000) (ψ := -133673/1000000) 259 251
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t440 : ((53094961663/1250000000000 : ℚ) : ℝ) ≤ stT259 440 := by
  have hc : ((111373/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53094961663/1250000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((111373/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c441 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((993189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291943/10000000) (δ := 819/62500000) (ψ := -133673/1000000) 259 251
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t441 : ((47292286041/1000000000000 : ℚ) : ℝ) ≤ stT259 441 := by
  have hc : ((993139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47292286041/1000000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((993139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c442 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((9533/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 175853/1000000) (δ := 12999/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t442 : ((36272669609/1000000000000 : ℚ) : ℝ) ≤ stT259 442 := by
  have hc : ((76259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36272669609/1000000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((76259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c443 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((55669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 644363/2000000) (δ := 13099/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t443 : ((13222185063/1000000000000 : ℚ) : ℝ) ≤ stT259 443 := by
  have hc : ((55659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13222185063/1000000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((55659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c444 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-297357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2340899/5000000) (δ := 13099/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t444 : ((-141143116653/10000000000000 : ℚ) : ℝ) ≤ stT259 444 := by
  have hc : ((-297407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141143116653/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-297407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c445 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-773659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6138479/10000000) (δ := 12999/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t445 : ((-183386828307/5000000000000 : ℚ) : ℝ) ≤ stT259 445 := by
  have hc : ((-773709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183386828307/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-773709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c446 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-994511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3795961/5000000) (δ := 13099/1000000000) (ψ := -133673/1000000) 259 251
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t446 : ((-235469278677/5000000000000 : ℚ) : ℝ) ≤ stT259 446 := by
  have hc : ((-994561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235469278677/5000000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-994561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c447 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-444593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66659/100000) (δ := 203/15625000) (ψ := -133673/1000000) 259 252
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t447 : ((-13143575007/312500000000 : ℚ) : ℝ) ≤ stT259 447 := by
  have hc : ((-222309/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13143575007/312500000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-222309/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c448 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-1544/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1304733/2500000) (δ := 3273/250000000) (ψ := -133673/1000000) 259 252
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t448 : ((-2918183541/125000000000 : ℚ) : ℝ) ≤ stT259 448 := by
  have hc : ((-49413/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).2
  have h0 : (0:ℝ) ≤ ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2918183541/125000000000 : ℚ) : ℝ)
      = ((59057/1250000 : ℚ) : ℝ) * ((-49413/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c449 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((60653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1887633/5000000) (δ := 3273/250000000) (ψ := -133673/1000000) 259 252
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t449 : ((28600313187/10000000000000 : ℚ) : ℝ) ≤ stT259 449 := by
  have hc : ((60603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28600313187/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((60603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c450 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((74337/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -583693/2500000) (δ := 13111/1000000000) (ψ := -133673/1000000) 259 252
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t450 : ((35039812873/1250000000000 : ℚ) : ℝ) ≤ stT259 450 := by
  have hc : ((297323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35039812873/1250000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((297323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c451 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((187251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224363/2500000) (δ := 203/15625000) (ψ := -133673/1000000) 259 252
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t451 : ((88168229321/2000000000000 : ℚ) : ℝ) ≤ stT259 451 := by
  have hc : ((187241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88168229321/2000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((187241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c452 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((19541/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 536631/10000000) (δ := 203/15625000) (ψ := -133673/1000000) 259 252
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t452 : ((11488543/250000000 : ℚ) : ℝ) ≤ stT259 452 := by
  have hc : ((977/1000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11488543/250000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((977/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c453 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((705943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 983803/5000000) (δ := 203/15625000) (ψ := -133673/1000000) 259 252
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t453 : ((4145709589/125000000000 : ℚ) : ℝ) ≤ stT259 453 := by
  have hc : ((705893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4145709589/125000000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((705893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c454 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((211059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212209/625000) (δ := 13111/1000000000) (ψ := -133673/1000000) 259 252
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t454 : ((99031376907/10000000000000 : ℚ) : ℝ) ≤ stT259 454 := by
  have hc : ((211009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99031376907/10000000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((211009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c455 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-34967/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2410019/5000000) (δ := 13011/1000000000) (ψ := -133673/1000000) 259 252
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t455 : ((-512348543/31250000000 : ℚ) : ℝ) ≤ stT259 455 := by
  have hc : ((-8743/25000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512348543/31250000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-8743/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c456 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-399559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6241559/10000000) (δ := 3273/250000000) (ψ := -133673/1000000) 259 252
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t456 : ((-5847574691/156250000000 : ℚ) : ℝ) ≤ stT259 456 := by
  have hc : ((-12487/15625 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5847574691/156250000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-12487/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c457 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-249247/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914977/2500000) (δ := 203/15625000) (ψ := -133673/1000000) 259 252
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t457 : ((-233197716339/5000000000000 : ℚ) : ℝ) ≤ stT259 457 := by
  have hc : ((-498519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233197716339/5000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-498519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c458 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-883041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26531/40000) (δ := 2617/200000000) (ψ := -133673/1000000) 259 253
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t458 : ((-41264193157/1000000000000 : ℚ) : ℝ) ≤ stT259 458 := by
  have hc : ((-883091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41264193157/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-883091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c459 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-494621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5220487/10000000) (δ := 6559/500000000) (ψ := -133673/1000000) 259 253
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t459 : ((-230893130631/10000000000000 : ℚ) : ℝ) ≤ stT259 459 := by
  have hc : ((-494671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230893130631/10000000000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-494671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c460 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((46221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1905699/5000000) (δ := 2597/200000000) (ψ := -133673/1000000) 259 253
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t460 : ((5381830273/2500000000000 : ℚ) : ℝ) ≤ stT259 460 := by
  have hc : ((46171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5381830273/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((46171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c461 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((285893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2405287/10000000) (δ := 2597/200000000) (ψ := -133673/1000000) 259 253
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t461 : ((16642734691/625000000000 : ℚ) : ℝ) ≤ stT259 461 := by
  have hc : ((71467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16642734691/625000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((71467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c462 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((184141/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -250571/2500000) (δ := 2597/200000000) (ψ := -133673/1000000) 259 253
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t462 : ((42832737351/1000000000000 : ℚ) : ℝ) ≤ stT259 462 := by
  have hc : ((184131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42832737351/1000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((184131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c463 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((987371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 397741/10000000) (δ := 6559/500000000) (ψ := -133673/1000000) 259 253
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t463 : ((458846574219/10000000000000 : ℚ) : ℝ) ≤ stT259 463 := by
  have hc : ((987321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458846574219/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((987321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c464 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((188299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897361/5000000) (δ := 6509/500000000) (ψ := -133673/1000000) 259 253
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t464 : ((87409748187/2500000000000 : ℚ) : ℝ) ≤ stT259 464 := by
  have hc : ((376573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87409748187/2500000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((376573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c465 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((291033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127549/400000) (δ := 6559/500000000) (ψ := -133673/1000000) 259 253
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t465 : ((67469937227/5000000000000 : ℚ) : ℝ) ≤ stT259 465 := by
  have hc : ((290983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67469937227/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((290983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c466 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-258121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1144921/2500000) (δ := 2597/200000000) (ψ := -133673/1000000) 259 253
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t466 : ((-59797825191/5000000000000 : ℚ) : ℝ) ≤ stT259 466 := by
  have hc : ((-258171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59797825191/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-258171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c467 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-182149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1193533/2000000) (δ := 2597/200000000) (ψ := -133673/1000000) 259 253
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t467 : ((-33717729327/1000000000000 : ℚ) : ℝ) ≤ stT259 467 := by
  have hc : ((-364323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33717729327/1000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-364323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c468 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-489981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1838167/2500000) (δ := 6559/500000000) (ψ := -133673/1000000) 259 253
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t468 : ((-113252881753/2500000000000 : ℚ) : ℝ) ≤ stT259 468 := by
  have hc : ((-245003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113252881753/2500000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-245003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c469 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-469289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6973207/10000000) (δ := 6489/500000000) (ψ := -133673/1000000) 259 254
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t469 : ((-54177373503/1250000000000 : ℚ) : ℝ) ≤ stT259 469 := by
  have hc : ((-234657/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54177373503/1250000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-234657/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c470 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-154627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5594097/10000000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 254
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t470 : ((-71329943607/2500000000000 : ℚ) : ℝ) ≤ stT259 470 := by
  have hc : ((-309279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71329943607/2500000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-309279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c471 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-116101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42179/100000) (δ := 521/40000000) (ψ := -133673/1000000) 259 254
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t471 : ((-6689949147/1250000000000 : ℚ) : ℝ) ≤ stT259 471 := by
  have hc : ((-116151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6689949147/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-116151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c472 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((8391/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2844617/10000000) (δ := 21/1600000) (ψ := -133673/1000000) 259 254
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t472 : ((386180793/20000000000 : ℚ) : ℝ) ≤ stT259 472 := by
  have hc : ((839/2000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386180793/20000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((839/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c473 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((207777/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184281/1250000) (δ := 21/1600000) (ψ := -133673/1000000) 259 254
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t473 : ((955301171/25000000000 : ℚ) : ℝ) ≤ stT259 473 := by
  have hc : ((415529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((955301171/25000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((415529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c474 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((999089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13341/1250000) (δ := 21/1600000) (ψ := -133673/1000000) 259 254
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t474 : ((91774719657/2000000000000 : ℚ) : ℝ) ≤ stT259 474 := by
  have hc : ((999039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91774719657/2000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((999039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c475 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((876067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 628939/5000000) (δ := 521/40000000) (ψ := -133673/1000000) 259 254
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t475 : ((401943756127/10000000000000 : ℚ) : ℝ) ≤ stT259 475 := by
  have hc : ((876017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401943756127/10000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((876017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c476 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((249727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 261957/1000000) (δ := 6539/500000000) (ψ := -133673/1000000) 259 254
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t476 : ((57225330999/2500000000000 : ℚ) : ℝ) ≤ stT259 476 := by
  have hc : ((124851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57225330999/2500000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((124851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c477 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-2571/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1989207/5000000) (δ := 521/40000000) (ψ := -133673/1000000) 259 254
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t477 : ((-4720171521/5000000000000 : ℚ) : ℝ) ≤ stT259 477 := by
  have hc : ((-10309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4720171521/5000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-10309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c478 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-13343/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5334473/10000000) (δ := 6489/500000000) (ψ := -133673/1000000) 259 254
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t478 : ((-2441410603/100000000000 : ℚ) : ℝ) ≤ stT259 478 := by
  have hc : ((-53377/100000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2441410603/100000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-53377/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c479 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-111641/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6687619/10000000) (δ := 21/1600000) (ψ := -133673/1000000) 259 254
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t479 : ((-12753242073/312500000000 : ℚ) : ℝ) ≤ stT259 479 := by
  have hc : ((-446589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12753242073/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-446589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c480 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-997291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7669919/10000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t480 : ((-113805584169/2500000000000 : ℚ) : ℝ) ≤ stT259 480 := by
  have hc : ((-997341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113805584169/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-997341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c481 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-409069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3161203/5000000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 255
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t481 : ((-93265454667/2500000000000 : ℚ) : ℝ) ≤ stT259 481 := by
  have hc : ((-204547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93265454667/2500000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-204547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c482 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-101997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2488807/5000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t482 : ((-1452003223/78125000000 : ℚ) : ℝ) ≤ stT259 482 := by
  have hc : ((-204019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1452003223/78125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-204019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c483 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((23253/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -363567/1000000) (δ := 12971/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t483 : ((2115182729/400000000000 : ℚ) : ℝ) ≤ stT259 483 := by
  have hc : ((23243/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2115182729/400000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((23243/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c484 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((606951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148223/5000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t484 : ((55172763009/2000000000000 : ℚ) : ℝ) ≤ stT259 484 := by
  have hc : ((606901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55172763009/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((606901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c485 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((927163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96007/1000000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 255
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t485 : ((105244940647/2500000000000 : ℚ) : ℝ) ≤ stT259 485 := by
  have hc : ((927113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105244940647/2500000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((927113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c486 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((247213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7473/200000) (δ := 12971/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t486 : ((224264743209/5000000000000 : ℚ) : ℝ) ≤ stT259 486 := by
  have hc : ((494401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224264743209/5000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((494401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c487 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((388209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 852293/5000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t487 : ((21987857789/625000000000 : ℚ) : ℝ) ≤ stT259 487 := by
  have hc : ((48523/62500 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21987857789/625000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((48523/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c488 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((350097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3032803/10000000) (δ := 12971/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t488 : ((79229287933/5000000000000 : ℚ) : ℝ) ≤ stT259 488 := by
  have hc : ((350047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79229287933/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((350047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c489 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-42911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1089559/2500000) (δ := 3283/250000000) (ψ := -133673/1000000) 259 255
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t489 : ((-4852673369/625000000000 : ℚ) : ℝ) ≤ stT259 489 := by
  have hc : ((-85847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4852673369/625000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-85847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c490 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-645447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5681013/10000000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t490 : ((-145802925869/5000000000000 : ℚ) : ℝ) ≤ stT259 490 := by
  have hc : ((-645497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145802925869/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-645497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c491 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-471187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437571/625000) (δ := 13071/1000000000) (ψ := -133673/1000000) 259 255
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t491 : ((-26581893541/625000000000 : ℚ) : ℝ) ≤ stT259 491 := by
  have hc : ((-117803/125000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26581893541/625000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-117803/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c492 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-15356/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7389423/10000000) (δ := 13139/1000000000) (ψ := -133673/1000000) 259 256
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t492 : ((-44309596639/1000000000000 : ℚ) : ℝ) ≤ stT259 492 := by
  have hc : ((-491417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44309596639/1000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-491417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c493 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-151451/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6074739/10000000) (δ := 13139/1000000000) (ψ := -133673/1000000) 259 256
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t493 : ((-34107351129/1000000000000 : ℚ) : ℝ) ≤ stT259 493 := by
  have hc : ((-151461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34107351129/1000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-151461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c494 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((-41009/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952529/2000000) (δ := 13139/1000000000) (ψ := -133673/1000000) 259 256
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t494 : ((-36907326621/2500000000000 : ℚ) : ℝ) ≤ stT259 494 := by
  have hc : ((-164061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36907326621/2500000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-164061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c495 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((47089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3453271/10000000) (δ := 3241/250000000) (ψ := -133673/1000000) 259 256
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t495 : ((21159286149/2500000000000 : ℚ) : ℝ) ≤ stT259 495 := by
  have hc : ((94153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21159286149/2500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((94153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c496 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((326751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073243/5000000) (δ := 13139/1000000000) (ψ := -133673/1000000) 259 256
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t496 : ((73352110719/2500000000000 : ℚ) : ℝ) ≤ stT259 496 := by
  have hc : ((163363/250000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73352110719/2500000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((163363/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c497 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((94377/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -842357/10000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 256
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t497 : ((10582899673/250000000000 : ℚ) : ℝ) ≤ stT259 497 := by
  have hc : ((23593/25000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10582899673/250000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((23593/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c498 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((61449/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229559/5000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 256
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t498 : ((22027608837/500000000000 : ℚ) : ℝ) ≤ stT259 498 := by
  have hc : ((491567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22027608837/500000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((491567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c499 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((95347/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1758003/10000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 256
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t499 : ((170721341943/5000000000000 : ℚ) : ℝ) ≤ stT259 499 := by
  have hc : ((381363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170721341943/5000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((381363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_c500 :
    |Real.cos (((259 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((342031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1527149/5000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 256
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st259_t500 : ((152938348953/10000000000000 : ℚ) : ℝ) ≤ stT259 500 := by
  have hc : ((341981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((259 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st259_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152938348953/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((341981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st259_p1 : ((991029/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT259 (i+1) := by
  rw [Finset.sum_range_one]
  exact st259_t1

theorem st259_p2 : ((10066135793/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT259 (i+1))
      = (∑ i ∈ Finset.range 1, stT259 (i+1)) + stT259 2 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 1
    simpa using h
  have hprev := st259_p1
  have hstep := st259_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p3 : ((497927550479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT259 (i+1))
      = (∑ i ∈ Finset.range 2, stT259 (i+1)) + stT259 3 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 2
    simpa using h
  have hprev := st259_p2
  have hstep := st259_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p4 : ((1128108800479/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT259 (i+1))
      = (∑ i ∈ Finset.range 3, stT259 (i+1)) + stT259 4 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 3
    simpa using h
  have hprev := st259_p3
  have hstep := st259_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p5 : ((393299960557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT259 (i+1))
      = (∑ i ∈ Finset.range 4, stT259 (i+1)) + stT259 5 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 4
    simpa using h
  have hprev := st259_p4
  have hstep := st259_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p6 : ((454239308331/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT259 (i+1))
      = (∑ i ∈ Finset.range 5, stT259 (i+1)) + stT259 6 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 5
    simpa using h
  have hprev := st259_p5
  have hstep := st259_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p7 : ((2462061004367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT259 (i+1))
      = (∑ i ∈ Finset.range 6, stT259 (i+1)) + stT259 7 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 6
    simpa using h
  have hprev := st259_p6
  have hstep := st259_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p8 : ((2331090682871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT259 (i+1))
      = (∑ i ∈ Finset.range 7, stT259 (i+1)) + stT259 8 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 7
    simpa using h
  have hprev := st259_p7
  have hstep := st259_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p9 : ((471462702619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT259 (i+1))
      = (∑ i ∈ Finset.range 8, stT259 (i+1)) + stT259 9 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 8
    simpa using h
  have hprev := st259_p8
  have hstep := st259_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p10 : ((4799076360787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT259 (i+1))
      = (∑ i ∈ Finset.range 9, stT259 (i+1)) + stT259 10 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 9
    simpa using h
  have hprev := st259_p9
  have hstep := st259_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p11 : ((6796082184303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT259 (i+1))
      = (∑ i ∈ Finset.range 10, stT259 (i+1)) + stT259 11 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 10
    simpa using h
  have hprev := st259_p10
  have hstep := st259_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p12 : ((807965739043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT259 (i+1))
      = (∑ i ∈ Finset.range 11, stT259 (i+1)) + stT259 12 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 11
    simpa using h
  have hprev := st259_p11
  have hstep := st259_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p13 : ((812768331643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT259 (i+1))
      = (∑ i ∈ Finset.range 12, stT259 (i+1)) + stT259 13 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 12
    simpa using h
  have hprev := st259_p12
  have hstep := st259_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p14 : ((4987980108187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT259 (i+1))
      = (∑ i ∈ Finset.range 13, stT259 (i+1)) + stT259 14 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 13
    simpa using h
  have hprev := st259_p13
  have hstep := st259_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p15 : ((868096532761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT259 (i+1))
      = (∑ i ∈ Finset.range 14, stT259 (i+1)) + stT259 15 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 14
    simpa using h
  have hprev := st259_p14
  have hstep := st259_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p16 : ((636101439963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT259 (i+1))
      = (∑ i ∈ Finset.range 15, stT259 (i+1)) + stT259 16 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 15
    simpa using h
  have hprev := st259_p15
  have hstep := st259_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p17 : ((26800571829/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT259 (i+1))
      = (∑ i ∈ Finset.range 16, stT259 (i+1)) + stT259 17 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 16
    simpa using h
  have hprev := st259_p16
  have hstep := st259_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p18 : ((1155422135673/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT259 (i+1))
      = (∑ i ∈ Finset.range 17, stT259 (i+1)) + stT259 18 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 17
    simpa using h
  have hprev := st259_p17
  have hstep := st259_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p19 : ((1407178876383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT259 (i+1))
      = (∑ i ∈ Finset.range 18, stT259 (i+1)) + stT259 19 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 18
    simpa using h
  have hprev := st259_p18
  have hstep := st259_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p20 : ((290776087989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT259 (i+1))
      = (∑ i ∈ Finset.range 19, stT259 (i+1)) + stT259 20 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 19
    simpa using h
  have hprev := st259_p19
  have hstep := st259_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p21 : ((-1583647289223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT259 (i+1))
      = (∑ i ∈ Finset.range 20, stT259 (i+1)) + stT259 21 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 20
    simpa using h
  have hprev := st259_p20
  have hstep := st259_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p22 : ((-3553667453391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT259 (i+1))
      = (∑ i ∈ Finset.range 21, stT259 (i+1)) + stT259 22 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 21
    simpa using h
  have hprev := st259_p21
  have hstep := st259_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p23 : ((-3813701716051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT259 (i+1))
      = (∑ i ∈ Finset.range 22, stT259 (i+1)) + stT259 23 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 22
    simpa using h
  have hprev := st259_p22
  have hstep := st259_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p24 : ((-1796204431363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT259 (i+1))
      = (∑ i ∈ Finset.range 23, stT259 (i+1)) + stT259 24 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 23
    simpa using h
  have hprev := st259_p23
  have hstep := st259_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p25 : ((-72825209327/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT259 (i+1))
      = (∑ i ∈ Finset.range 24, stT259 (i+1)) + stT259 25 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 24
    simpa using h
  have hprev := st259_p24
  have hstep := st259_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p26 : ((-1603259279943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT259 (i+1))
      = (∑ i ∈ Finset.range 25, stT259 (i+1)) + stT259 26 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 25
    simpa using h
  have hprev := st259_p25
  have hstep := st259_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p27 : ((-904367482443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT259 (i+1))
      = (∑ i ∈ Finset.range 26, stT259 (i+1)) + stT259 27 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 26
    simpa using h
  have hprev := st259_p26
  have hstep := st259_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p28 : ((-3174300276633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT259 (i+1))
      = (∑ i ∈ Finset.range 27, stT259 (i+1)) + stT259 28 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 27
    simpa using h
  have hprev := st259_p27
  have hstep := st259_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p29 : ((-2331191619949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT259 (i+1))
      = (∑ i ∈ Finset.range 28, stT259 (i+1)) + stT259 29 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 28
    simpa using h
  have hprev := st259_p28
  have hstep := st259_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p30 : ((-2017087486827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT259 (i+1))
      = (∑ i ∈ Finset.range 29, stT259 (i+1)) + stT259 30 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 29
    simpa using h
  have hprev := st259_p29
  have hstep := st259_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p31 : ((-3622005420147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT259 (i+1))
      = (∑ i ∈ Finset.range 30, stT259 (i+1)) + stT259 31 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 30
    simpa using h
  have hprev := st259_p30
  have hstep := st259_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p32 : ((-2312150918191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT259 (i+1))
      = (∑ i ∈ Finset.range 31, stT259 (i+1)) + stT259 32 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 31
    simpa using h
  have hprev := st259_p31
  have hstep := st259_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p33 : ((-1300286571119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT259 (i+1))
      = (∑ i ∈ Finset.range 32, stT259 (i+1)) + stT259 33 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 32
    simpa using h
  have hprev := st259_p32
  have hstep := st259_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p34 : ((-2564049464603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT259 (i+1))
      = (∑ i ∈ Finset.range 33, stT259 (i+1)) + stT259 34 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 33
    simpa using h
  have hprev := st259_p33
  have hstep := st259_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p35 : ((-507716567659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT259 (i+1))
      = (∑ i ∈ Finset.range 34, stT259 (i+1)) + stT259 35 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 34
    simpa using h
  have hprev := st259_p34
  have hstep := st259_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p36 : ((-2093804616557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT259 (i+1))
      = (∑ i ∈ Finset.range 35, stT259 (i+1)) + stT259 36 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 35
    simpa using h
  have hprev := st259_p35
  have hstep := st259_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p37 : ((-3082077594273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT259 (i+1))
      = (∑ i ∈ Finset.range 36, stT259 (i+1)) + stT259 37 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 36
    simpa using h
  have hprev := st259_p36
  have hstep := st259_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p38 : ((-1495351147737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT259 (i+1))
      = (∑ i ∈ Finset.range 37, stT259 (i+1)) + stT259 38 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 37
    simpa using h
  have hprev := st259_p37
  have hstep := st259_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p39 : ((9884437/1600000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT259 (i+1))
      = (∑ i ∈ Finset.range 38, stT259 (i+1)) + stT259 39 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 38
    simpa using h
  have hprev := st259_p38
  have hstep := st259_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p40 : ((721090387661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT259 (i+1))
      = (∑ i ∈ Finset.range 39, stT259 (i+1)) + stT259 40 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 39
    simpa using h
  have hprev := st259_p39
  have hstep := st259_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p41 : ((169488741079/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT259 (i+1))
      = (∑ i ∈ Finset.range 40, stT259 (i+1)) + stT259 41 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 40
    simpa using h
  have hprev := st259_p40
  have hstep := st259_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p42 : ((4002790701549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT259 (i+1))
      = (∑ i ∈ Finset.range 41, stT259 (i+1)) + stT259 42 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 41
    simpa using h
  have hprev := st259_p41
  have hstep := st259_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p43 : ((1353182327041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT259 (i+1))
      = (∑ i ∈ Finset.range 42, stT259 (i+1)) + stT259 43 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 42
    simpa using h
  have hprev := st259_p42
  have hstep := st259_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p44 : ((345866223409/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT259 (i+1))
      = (∑ i ∈ Finset.range 43, stT259 (i+1)) + stT259 44 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 43
    simpa using h
  have hprev := st259_p43
  have hstep := st259_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p45 : ((8289793762371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT259 (i+1))
      = (∑ i ∈ Finset.range 44, stT259 (i+1)) + stT259 45 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 44
    simpa using h
  have hprev := st259_p44
  have hstep := st259_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p46 : ((4548437252181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT259 (i+1))
      = (∑ i ∈ Finset.range 45, stT259 (i+1)) + stT259 46 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 45
    simpa using h
  have hprev := st259_p45
  have hstep := st259_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p47 : ((1112785412639/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT259 (i+1))
      = (∑ i ∈ Finset.range 46, stT259 (i+1)) + stT259 47 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 46
    simpa using h
  have hprev := st259_p46
  have hstep := st259_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p48 : ((964552501659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT259 (i+1))
      = (∑ i ∈ Finset.range 47, stT259 (i+1)) + stT259 48 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 47
    simpa using h
  have hprev := st259_p47
  have hstep := st259_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p49 : ((49747808389/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT259 (i+1))
      = (∑ i ∈ Finset.range 48, stT259 (i+1)) + stT259 49 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 48
    simpa using h
  have hprev := st259_p48
  have hstep := st259_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p50 : ((3054441478221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT259 (i+1))
      = (∑ i ∈ Finset.range 49, stT259 (i+1)) + stT259 50 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 49
    simpa using h
  have hprev := st259_p49
  have hstep := st259_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p51 : ((3632060478921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT259 (i+1))
      = (∑ i ∈ Finset.range 50, stT259 (i+1)) + stT259 51 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 50
    simpa using h
  have hprev := st259_p50
  have hstep := st259_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p52 : ((2091290060523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT259 (i+1))
      = (∑ i ∈ Finset.range 51, stT259 (i+1)) + stT259 52 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 51
    simpa using h
  have hprev := st259_p51
  have hstep := st259_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p53 : ((1947399337599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT259 (i+1))
      = (∑ i ∈ Finset.range 52, stT259 (i+1)) + stT259 53 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 52
    simpa using h
  have hprev := st259_p52
  have hstep := st259_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p54 : ((1622718024251/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT259 (i+1))
      = (∑ i ∈ Finset.range 53, stT259 (i+1)) + stT259 54 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 53
    simpa using h
  have hprev := st259_p53
  have hstep := st259_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p55 : ((6841896763477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT259 (i+1))
      = (∑ i ∈ Finset.range 54, stT259 (i+1)) + stT259 55 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 54
    simpa using h
  have hprev := st259_p54
  have hstep := st259_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p56 : ((8114841814487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT259 (i+1))
      = (∑ i ∈ Finset.range 55, stT259 (i+1)) + stT259 56 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 55
    simpa using h
  have hprev := st259_p55
  have hstep := st259_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p57 : ((3776979521953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT259 (i+1))
      = (∑ i ∈ Finset.range 56, stT259 (i+1)) + stT259 57 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 56
    simpa using h
  have hprev := st259_p56
  have hstep := st259_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p58 : ((3252357531853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT259 (i+1))
      = (∑ i ∈ Finset.range 57, stT259 (i+1)) + stT259 58 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 57
    simpa using h
  have hprev := st259_p57
  have hstep := st259_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p59 : ((7548313191773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT259 (i+1))
      = (∑ i ∈ Finset.range 58, stT259 (i+1)) + stT259 59 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 58
    simpa using h
  have hprev := st259_p58
  have hstep := st259_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p60 : ((7906747347921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT259 (i+1))
      = (∑ i ∈ Finset.range 59, stT259 (i+1)) + stT259 60 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 59
    simpa using h
  have hprev := st259_p59
  have hstep := st259_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p61 : ((3320336833903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT259 (i+1))
      = (∑ i ∈ Finset.range 60, stT259 (i+1)) + stT259 61 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 60
    simpa using h
  have hprev := st259_p60
  have hstep := st259_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p62 : ((3705017596801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT259 (i+1))
      = (∑ i ∈ Finset.range 61, stT259 (i+1)) + stT259 62 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 61
    simpa using h
  have hprev := st259_p61
  have hstep := st259_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p63 : ((7843972226789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT259 (i+1))
      = (∑ i ∈ Finset.range 62, stT259 (i+1)) + stT259 63 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 62
    simpa using h
  have hprev := st259_p62
  have hstep := st259_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p64 : ((664324751621/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT259 (i+1))
      = (∑ i ∈ Finset.range 63, stT259 (i+1)) + stT259 64 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 63
    simpa using h
  have hprev := st259_p63
  have hstep := st259_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p65 : ((479524419359/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT259 (i+1))
      = (∑ i ∈ Finset.range 64, stT259 (i+1)) + stT259 65 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 64
    simpa using h
  have hprev := st259_p64
  have hstep := st259_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p66 : ((7468924152989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT259 (i+1))
      = (∑ i ∈ Finset.range 65, stT259 (i+1)) + stT259 66 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 65
    simpa using h
  have hprev := st259_p65
  have hstep := st259_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p67 : ((1697997265491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT259 (i+1))
      = (∑ i ∈ Finset.range 66, stT259 (i+1)) + stT259 67 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 66
    simpa using h
  have hprev := st259_p66
  have hstep := st259_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p68 : ((994329905469/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT259 (i+1))
      = (∑ i ∈ Finset.range 67, stT259 (i+1)) + stT259 68 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 67
    simpa using h
  have hprev := st259_p67
  have hstep := st259_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p69 : ((3412149956441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT259 (i+1))
      = (∑ i ∈ Finset.range 68, stT259 (i+1)) + stT259 69 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 68
    simpa using h
  have hprev := st259_p68
  have hstep := st259_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p70 : ((3766266132141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT259 (i+1))
      = (∑ i ∈ Finset.range 69, stT259 (i+1)) + stT259 70 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 69
    simpa using h
  have hprev := st259_p69
  have hstep := st259_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p71 : ((1852888816887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT259 (i+1))
      = (∑ i ∈ Finset.range 70, stT259 (i+1)) + stT259 71 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 70
    simpa using h
  have hprev := st259_p70
  have hstep := st259_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p72 : ((1743920356459/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT259 (i+1))
      = (∑ i ∈ Finset.range 71, stT259 (i+1)) + stT259 72 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 71
    simpa using h
  have hprev := st259_p71
  have hstep := st259_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p73 : ((1955767088281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT259 (i+1))
      = (∑ i ∈ Finset.range 72, stT259 (i+1)) + stT259 73 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 72
    simpa using h
  have hprev := st259_p72
  have hstep := st259_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p74 : ((6742972610683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT259 (i+1))
      = (∑ i ∈ Finset.range 73, stT259 (i+1)) + stT259 74 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 73
    simpa using h
  have hprev := st259_p73
  have hstep := st259_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p75 : ((7896502899583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT259 (i+1))
      = (∑ i ∈ Finset.range 74, stT259 (i+1)) + stT259 75 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 74
    simpa using h
  have hprev := st259_p74
  have hstep := st259_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p76 : ((3391815471221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT259 (i+1))
      = (∑ i ∈ Finset.range 75, stT259 (i+1)) + stT259 76 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 75
    simpa using h
  have hprev := st259_p75
  have hstep := st259_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p77 : ((7789559136337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT259 (i+1))
      = (∑ i ∈ Finset.range 76, stT259 (i+1)) + stT259 77 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 76
    simpa using h
  have hprev := st259_p76
  have hstep := st259_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p78 : ((6915879844201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT259 (i+1))
      = (∑ i ∈ Finset.range 77, stT259 (i+1)) + stT259 78 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 77
    simpa using h
  have hprev := st259_p77
  have hstep := st259_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p79 : ((3830316154469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT259 (i+1))
      = (∑ i ∈ Finset.range 78, stT259 (i+1)) + stT259 79 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 78
    simpa using h
  have hprev := st259_p78
  have hstep := st259_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p80 : ((1755671924677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT259 (i+1))
      = (∑ i ∈ Finset.range 79, stT259 (i+1)) + stT259 80 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 79
    simpa using h
  have hprev := st259_p79
  have hstep := st259_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p81 : ((3792807154541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT259 (i+1))
      = (∑ i ∈ Finset.range 80, stT259 (i+1)) + stT259 81 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 80
    simpa using h
  have hprev := st259_p80
  have hstep := st259_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p82 : ((3530501183693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT259 (i+1))
      = (∑ i ∈ Finset.range 81, stT259 (i+1)) + stT259 82 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 81
    simpa using h
  have hprev := st259_p81
  have hstep := st259_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p83 : ((94805120777/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT259 (i+1))
      = (∑ i ∈ Finset.range 82, stT259 (i+1)) + stT259 83 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 82
    simpa using h
  have hprev := st259_p82
  have hstep := st259_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p84 : ((702629857863/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT259 (i+1))
      = (∑ i ∈ Finset.range 83, stT259 (i+1)) + stT259 84 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 83
    simpa using h
  have hprev := st259_p83
  have hstep := st259_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p85 : ((3825295322809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT259 (i+1))
      = (∑ i ∈ Finset.range 84, stT259 (i+1)) + stT259 85 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 84
    simpa using h
  have hprev := st259_p84
  have hstep := st259_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p86 : ((693490327369/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT259 (i+1))
      = (∑ i ∈ Finset.range 85, stT259 (i+1)) + stT259 86 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 85
    simpa using h
  have hprev := st259_p85
  have hstep := st259_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p87 : ((3878186320941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT259 (i+1))
      = (∑ i ∈ Finset.range 86, stT259 (i+1)) + stT259 87 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 86
    simpa using h
  have hprev := st259_p86
  have hstep := st259_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p88 : ((3414614760467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT259 (i+1))
      = (∑ i ∈ Finset.range 87, stT259 (i+1)) + stT259 88 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 87
    simpa using h
  have hprev := st259_p87
  have hstep := st259_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p89 : ((7841451396147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT259 (i+1))
      = (∑ i ∈ Finset.range 88, stT259 (i+1)) + stT259 89 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 88
    simpa using h
  have hprev := st259_p88
  have hstep := st259_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p90 : ((339440704929/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT259 (i+1))
      = (∑ i ∈ Finset.range 89, stT259 (i+1)) + stT259 90 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 89
    simpa using h
  have hprev := st259_p89
  have hstep := st259_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p91 : ((976293105327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT259 (i+1))
      = (∑ i ∈ Finset.range 90, stT259 (i+1)) + stT259 91 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 90
    simpa using h
  have hprev := st259_p90
  have hstep := st259_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p92 : ((6914546312129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT259 (i+1))
      = (∑ i ∈ Finset.range 91, stT259 (i+1)) + stT259 92 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 91
    simpa using h
  have hprev := st259_p91
  have hstep := st259_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p93 : ((1515242045583/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT259 (i+1))
      = (∑ i ∈ Finset.range 92, stT259 (i+1)) + stT259 93 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 92
    simpa using h
  have hprev := st259_p92
  have hstep := st259_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p94 : ((7251155521771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT259 (i+1))
      = (∑ i ∈ Finset.range 93, stT259 (i+1)) + stT259 94 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 93
    simpa using h
  have hprev := st259_p93
  have hstep := st259_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p95 : ((7168843278559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT259 (i+1))
      = (∑ i ∈ Finset.range 94, stT259 (i+1)) + stT259 95 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 94
    simpa using h
  have hprev := st259_p94
  have hstep := st259_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p96 : ((7666848683839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT259 (i+1))
      = (∑ i ∈ Finset.range 95, stT259 (i+1)) + stT259 96 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 95
    simpa using h
  have hprev := st259_p95
  have hstep := st259_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p97 : ((1707684460927/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT259 (i+1))
      = (∑ i ∈ Finset.range 96, stT259 (i+1)) + stT259 97 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 96
    simpa using h
  have hprev := st259_p96
  have hstep := st259_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p98 : ((1958447118787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT259 (i+1))
      = (∑ i ∈ Finset.range 97, stT259 (i+1)) + stT259 98 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 97
    simpa using h
  have hprev := st259_p97
  have hstep := st259_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p99 : ((3452833519163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT259 (i+1))
      = (∑ i ∈ Finset.range 98, stT259 (i+1)) + stT259 99 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 98
    simpa using h
  have hprev := st259_p98
  have hstep := st259_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p100 : ((7501471442521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT259 (i+1))
      = (∑ i ∈ Finset.range 99, stT259 (i+1)) + stT259 100 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 99
    simpa using h
  have hprev := st259_p99
  have hstep := st259_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p101 : ((7427964005309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT259 (i+1))
      = (∑ i ∈ Finset.range 100, stT259 (i+1)) + stT259 101 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 100
    simpa using h
  have hprev := st259_p100
  have hstep := st259_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p102 : ((6939408149593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT259 (i+1))
      = (∑ i ∈ Finset.range 101, stT259 (i+1)) + stT259 102 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 101
    simpa using h
  have hprev := st259_p101
  have hstep := st259_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p103 : ((3915402375347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT259 (i+1))
      = (∑ i ∈ Finset.range 102, stT259 (i+1)) + stT259 103 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 102
    simpa using h
  have hprev := st259_p102
  have hstep := st259_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p104 : ((1717385789389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT259 (i+1))
      = (∑ i ∈ Finset.range 103, stT259 (i+1)) + stT259 104 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 103
    simpa using h
  have hprev := st259_p103
  have hstep := st259_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p105 : ((469037337241/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT259 (i+1))
      = (∑ i ∈ Finset.range 104, stT259 (i+1)) + stT259 105 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 104
    simpa using h
  have hprev := st259_p104
  have hstep := st259_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p106 : ((935396353337/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT259 (i+1))
      = (∑ i ∈ Finset.range 105, stT259 (i+1)) + stT259 106 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 105
    simpa using h
  have hprev := st259_p105
  have hstep := st259_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p107 : ((858691572809/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT259 (i+1))
      = (∑ i ∈ Finset.range 106, stT259 (i+1)) + stT259 107 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 106
    simpa using h
  have hprev := st259_p106
  have hstep := st259_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p108 : ((1955199865243/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT259 (i+1))
      = (∑ i ∈ Finset.range 107, stT259 (i+1)) + stT259 108 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 107
    simpa using h
  have hprev := st259_p107
  have hstep := st259_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p109 : ((7032169727041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT259 (i+1))
      = (∑ i ∈ Finset.range 108, stT259 (i+1)) + stT259 109 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 108
    simpa using h
  have hprev := st259_p108
  have hstep := st259_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p110 : ((1442612488921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT259 (i+1))
      = (∑ i ∈ Finset.range 109, stT259 (i+1)) + stT259 110 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 109
    simpa using h
  have hprev := st259_p109
  have hstep := st259_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p111 : ((3877107882871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT259 (i+1))
      = (∑ i ∈ Finset.range 110, stT259 (i+1)) + stT259 111 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 110
    simpa using h
  have hprev := st259_p110
  have hstep := st259_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p112 : ((3409608891223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT259 (i+1))
      = (∑ i ∈ Finset.range 111, stT259 (i+1)) + stT259 112 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 111
    simpa using h
  have hprev := st259_p111
  have hstep := st259_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p113 : ((3771145460903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT259 (i+1))
      = (∑ i ∈ Finset.range 112, stT259 (i+1)) + stT259 113 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 112
    simpa using h
  have hprev := st259_p112
  have hstep := st259_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p114 : ((3763095504233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT259 (i+1))
      = (∑ i ∈ Finset.range 113, stT259 (i+1)) + stT259 114 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 113
    simpa using h
  have hprev := st259_p113
  have hstep := st259_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p115 : ((3408989785553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT259 (i+1))
      = (∑ i ∈ Finset.range 114, stT259 (i+1)) + stT259 115 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 114
    simpa using h
  have hprev := st259_p114
  have hstep := st259_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p116 : ((3864780046667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT259 (i+1))
      = (∑ i ∈ Finset.range 115, stT259 (i+1)) + stT259 116 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 115
    simpa using h
  have hprev := st259_p115
  have hstep := st259_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p117 : ((3658875183947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT259 (i+1))
      = (∑ i ∈ Finset.range 116, stT259 (i+1)) + stT259 117 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 116
    simpa using h
  have hprev := st259_p116
  have hstep := st259_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p118 : ((6896107685819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT259 (i+1))
      = (∑ i ∈ Finset.range 117, stT259 (i+1)) + stT259 118 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 117
    simpa using h
  have hprev := st259_p117
  have hstep := st259_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p119 : ((7803899964749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT259 (i+1))
      = (∑ i ∈ Finset.range 118, stT259 (i+1)) + stT259 119 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 118
    simpa using h
  have hprev := st259_p118
  have hstep := st259_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p120 : ((7191197381227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT259 (i+1))
      = (∑ i ∈ Finset.range 119, stT259 (i+1)) + stT259 120 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 119
    simpa using h
  have hprev := st259_p119
  have hstep := st259_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p121 : ((348027276999/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT259 (i+1))
      = (∑ i ∈ Finset.range 120, stT259 (i+1)) + stT259 121 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 120
    simpa using h
  have hprev := st259_p120
  have hstep := st259_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p122 : ((7824226241199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT259 (i+1))
      = (∑ i ∈ Finset.range 121, stT259 (i+1)) + stT259 122 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 121
    simpa using h
  have hprev := st259_p121
  have hstep := st259_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p123 : ((7148006201319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT259 (i+1))
      = (∑ i ∈ Finset.range 122, stT259 (i+1)) + stT259 123 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 122
    simpa using h
  have hprev := st259_p122
  have hstep := st259_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p124 : ((1743161443737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT259 (i+1))
      = (∑ i ∈ Finset.range 123, stT259 (i+1)) + stT259 124 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 123
    simpa using h
  have hprev := st259_p123
  have hstep := st259_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p125 : ((782355532369/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT259 (i+1))
      = (∑ i ∈ Finset.range 124, stT259 (i+1)) + stT259 125 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 124
    simpa using h
  have hprev := st259_p124
  have hstep := st259_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p126 : ((7180710827929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT259 (i+1))
      = (∑ i ∈ Finset.range 125, stT259 (i+1)) + stT259 126 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 125
    simpa using h
  have hprev := st259_p125
  have hstep := st259_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p127 : ((1732125446151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT259 (i+1))
      = (∑ i ∈ Finset.range 126, stT259 (i+1)) + stT259 127 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 126
    simpa using h
  have hprev := st259_p126
  have hstep := st259_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p128 : ((3899615418899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT259 (i+1))
      = (∑ i ∈ Finset.range 127, stT259 (i+1)) + stT259 128 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 127
    simpa using h
  have hprev := st259_p127
  have hstep := st259_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p129 : ((3644797051381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT259 (i+1))
      = (∑ i ∈ Finset.range 128, stT259 (i+1)) + stT259 129 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 128
    simpa using h
  have hprev := st259_p128
  have hstep := st259_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p130 : ((6850446276167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT259 (i+1))
      = (∑ i ∈ Finset.range 129, stT259 (i+1)) + stT259 130 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 129
    simpa using h
  have hprev := st259_p129
  have hstep := st259_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p131 : ((7718781365087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT259 (i+1))
      = (∑ i ∈ Finset.range 130, stT259 (i+1)) + stT259 131 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 130
    simpa using h
  have hprev := st259_p130
  have hstep := st259_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p132 : ((7471237511153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT259 (i+1))
      = (∑ i ∈ Finset.range 131, stT259 (i+1)) + stT259 132 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 131
    simpa using h
  have hprev := st259_p131
  have hstep := st259_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p133 : ((6792755152113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT259 (i+1))
      = (∑ i ∈ Finset.range 132, stT259 (i+1)) + stT259 133 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 132
    simpa using h
  have hprev := st259_p132
  have hstep := st259_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p134 : ((7538390722161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT259 (i+1))
      = (∑ i ∈ Finset.range 133, stT259 (i+1)) + stT259 134 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 133
    simpa using h
  have hprev := st259_p133
  have hstep := st259_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p135 : ((1537536574801/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT259 (i+1))
      = (∑ i ∈ Finset.range 134, stT259 (i+1)) + stT259 135 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 134
    simpa using h
  have hprev := st259_p134
  have hstep := st259_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p136 : ((6841970112839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT259 (i+1))
      = (∑ i ∈ Finset.range 135, stT259 (i+1)) + stT259 136 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 135
    simpa using h
  have hprev := st259_p135
  have hstep := st259_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p137 : ((289848296747/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT259 (i+1))
      = (∑ i ∈ Finset.range 136, stT259 (i+1)) + stT259 137 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 136
    simpa using h
  have hprev := st259_p136
  have hstep := st259_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p138 : ((1567143844759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT259 (i+1))
      = (∑ i ∈ Finset.range 137, stT259 (i+1)) + stT259 138 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 137
    simpa using h
  have hprev := st259_p137
  have hstep := st259_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p139 : ((1415569077703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT259 (i+1))
      = (∑ i ∈ Finset.range 138, stT259 (i+1)) + stT259 139 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 138
    simpa using h
  have hprev := st259_p138
  have hstep := st259_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p140 : ((692654658557/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT259 (i+1))
      = (∑ i ∈ Finset.range 139, stT259 (i+1)) + stT259 140 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 139
    simpa using h
  have hprev := st259_p139
  have hstep := st259_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p141 : ((7765041808079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT259 (i+1))
      = (∑ i ∈ Finset.range 140, stT259 (i+1)) + stT259 141 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 140
    simpa using h
  have hprev := st259_p140
  have hstep := st259_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p142 : ((7475449330881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT259 (i+1))
      = (∑ i ∈ Finset.range 141, stT259 (i+1)) + stT259 142 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 141
    simpa using h
  have hprev := st259_p141
  have hstep := st259_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p143 : ((6784774494863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT259 (i+1))
      = (∑ i ∈ Finset.range 142, stT259 (i+1)) + stT259 143 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 142
    simpa using h
  have hprev := st259_p142
  have hstep := st259_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p144 : ((740142341487/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT259 (i+1))
      = (∑ i ∈ Finset.range 143, stT259 (i+1)) + stT259 144 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 143
    simpa using h
  have hprev := st259_p143
  have hstep := st259_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p145 : ((3905591352867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT259 (i+1))
      = (∑ i ∈ Finset.range 144, stT259 (i+1)) + stT259 145 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 144
    simpa using h
  have hprev := st259_p144
  have hstep := st259_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p146 : ((351108853859/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT259 (i+1))
      = (∑ i ∈ Finset.range 145, stT259 (i+1)) + stT259 146 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 145
    simpa using h
  have hprev := st259_p145
  have hstep := st259_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p147 : ((1732964900383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT259 (i+1))
      = (∑ i ∈ Finset.range 146, stT259 (i+1)) + stT259 147 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 146
    simpa using h
  have hprev := st259_p146
  have hstep := st259_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p148 : ((3875736142457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT259 (i+1))
      = (∑ i ∈ Finset.range 147, stT259 (i+1)) + stT259 148 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 147
    simpa using h
  have hprev := st259_p147
  have hstep := st259_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p149 : ((3774848131273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT259 (i+1))
      = (∑ i ∈ Finset.range 148, stT259 (i+1)) + stT259 149 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 148
    simpa using h
  have hprev := st259_p148
  have hstep := st259_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p150 : ((6800970963037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT259 (i+1))
      = (∑ i ∈ Finset.range 149, stT259 (i+1)) + stT259 150 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 149
    simpa using h
  have hprev := st259_p149
  have hstep := st259_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p151 : ((7233611587781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT259 (i+1))
      = (∑ i ∈ Finset.range 150, stT259 (i+1)) + stT259 151 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 150
    simpa using h
  have hprev := st259_p150
  have hstep := st259_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p152 : ((7854265797539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT259 (i+1))
      = (∑ i ∈ Finset.range 151, stT259 (i+1)) + stT259 152 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 151
    simpa using h
  have hprev := st259_p151
  have hstep := st259_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p153 : ((1451862136537/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT259 (i+1))
      = (∑ i ∈ Finset.range 152, stT259 (i+1)) + stT259 153 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 152
    simpa using h
  have hprev := st259_p152
  have hstep := st259_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p154 : ((6786258737119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT259 (i+1))
      = (∑ i ∈ Finset.range 153, stT259 (i+1)) + stT259 154 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 153
    simpa using h
  have hprev := st259_p153
  have hstep := st259_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p155 : ((1870641318031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT259 (i+1))
      = (∑ i ∈ Finset.range 154, stT259 (i+1)) + stT259 155 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 154
    simpa using h
  have hprev := st259_p154
  have hstep := st259_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p156 : ((1953516965551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT259 (i+1))
      = (∑ i ∈ Finset.range 155, stT259 (i+1)) + stT259 156 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 155
    simpa using h
  have hprev := st259_p155
  have hstep := st259_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p157 : ((7062372861427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT259 (i+1))
      = (∑ i ∈ Finset.range 156, stT259 (i+1)) + stT259 157 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 156
    simpa using h
  have hprev := st259_p156
  have hstep := st259_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p158 : ((1370158205819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT259 (i+1))
      = (∑ i ∈ Finset.range 157, stT259 (i+1)) + stT259 158 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 157
    simpa using h
  have hprev := st259_p157
  have hstep := st259_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p159 : ((7627057897731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT259 (i+1))
      = (∑ i ∈ Finset.range 158, stT259 (i+1)) + stT259 159 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 158
    simpa using h
  have hprev := st259_p158
  have hstep := st259_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p160 : ((24210523371/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT259 (i+1))
      = (∑ i ∈ Finset.range 159, stT259 (i+1)) + stT259 160 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 159
    simpa using h
  have hprev := st259_p159
  have hstep := st259_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p161 : ((1392794664611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT259 (i+1))
      = (∑ i ∈ Finset.range 160, stT259 (i+1)) + stT259 161 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 160
    simpa using h
  have hprev := st259_p160
  have hstep := st259_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p162 : ((1380700926471/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT259 (i+1))
      = (∑ i ∈ Finset.range 161, stT259 (i+1)) + stT259 162 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 161
    simpa using h
  have hprev := st259_p161
  have hstep := st259_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p163 : ((1537117321863/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT259 (i+1))
      = (∑ i ∈ Finset.range 162, stT259 (i+1)) + stT259 163 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 162
    simpa using h
  have hprev := st259_p162
  have hstep := st259_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p164 : ((7717263300603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT259 (i+1))
      = (∑ i ∈ Finset.range 163, stT259 (i+1)) + stT259 164 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 163
    simpa using h
  have hprev := st259_p163
  have hstep := st259_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p165 : ((693925709047/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT259 (i+1))
      = (∑ i ∈ Finset.range 164, stT259 (i+1)) + stT259 165 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 164
    simpa using h
  have hprev := st259_p164
  have hstep := st259_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p166 : ((690600678163/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT259 (i+1))
      = (∑ i ∈ Finset.range 165, stT259 (i+1)) + stT259 166 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 165
    simpa using h
  have hprev := st259_p165
  have hstep := st259_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p167 : ((7678488746371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT259 (i+1))
      = (∑ i ∈ Finset.range 166, stT259 (i+1)) + stT259 167 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 166
    simpa using h
  have hprev := st259_p166
  have hstep := st259_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p168 : ((7742074009027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT259 (i+1))
      = (∑ i ∈ Finset.range 167, stT259 (i+1)) + stT259 168 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 167
    simpa using h
  have hprev := st259_p167
  have hstep := st259_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p169 : ((872249510937/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT259 (i+1))
      = (∑ i ∈ Finset.range 168, stT259 (i+1)) + stT259 169 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 168
    simpa using h
  have hprev := st259_p168
  have hstep := st259_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p170 : ((3428255182713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT259 (i+1))
      = (∑ i ∈ Finset.range 169, stT259 (i+1)) + stT259 170 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 169
    simpa using h
  have hprev := st259_p169
  have hstep := st259_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p171 : ((3802135478441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT259 (i+1))
      = (∑ i ∈ Finset.range 170, stT259 (i+1)) + stT259 171 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 170
    simpa using h
  have hprev := st259_p170
  have hstep := st259_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p172 : ((3904301019029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT259 (i+1))
      = (∑ i ∈ Finset.range 171, stT259 (i+1)) + stT259 172 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 171
    simpa using h
  have hprev := st259_p171
  have hstep := st259_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p173 : ((354598849109/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT259 (i+1))
      = (∑ i ∈ Finset.range 172, stT259 (i+1)) + stT259 173 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 172
    simpa using h
  have hprev := st259_p172
  have hstep := st259_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p174 : ((1356744511459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT259 (i+1))
      = (∑ i ∈ Finset.range 173, stT259 (i+1)) + stT259 174 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 173
    simpa using h
  have hprev := st259_p173
  have hstep := st259_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p175 : ((297806684663/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT259 (i+1))
      = (∑ i ∈ Finset.range 174, stT259 (i+1)) + stT259 175 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 174
    simpa using h
  have hprev := st259_p174
  have hstep := st259_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p176 : ((7870900177197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT259 (i+1))
      = (∑ i ∈ Finset.range 175, stT259 (i+1)) + stT259 176 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 175
    simpa using h
  have hprev := st259_p175
  have hstep := st259_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p177 : ((3648860241321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT259 (i+1))
      = (∑ i ∈ Finset.range 176, stT259 (i+1)) + stT259 177 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 176
    simpa using h
  have hprev := st259_p176
  have hstep := st259_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p178 : ((3376051205451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT259 (i+1))
      = (∑ i ∈ Finset.range 177, stT259 (i+1)) + stT259 178 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 177
    simpa using h
  have hprev := st259_p177
  have hstep := st259_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p179 : ((1798969248363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT259 (i+1))
      = (∑ i ∈ Finset.range 178, stT259 (i+1)) + stT259 179 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 178
    simpa using h
  have hprev := st259_p178
  have hstep := st259_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p180 : ((3923563971641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT259 (i+1))
      = (∑ i ∈ Finset.range 179, stT259 (i+1)) + stT259 180 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 179
    simpa using h
  have hprev := st259_p179
  have hstep := st259_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p181 : ((7576948387027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT259 (i+1))
      = (∑ i ∈ Finset.range 180, stT259 (i+1)) + stT259 181 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 180
    simpa using h
  have hprev := st259_p180
  have hstep := st259_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p182 : ((6854869335777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT259 (i+1))
      = (∑ i ∈ Finset.range 181, stT259 (i+1)) + stT259 182 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 181
    simpa using h
  have hprev := st259_p181
  have hstep := st259_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p183 : ((6911357647713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT259 (i+1))
      = (∑ i ∈ Finset.range 182, stT259 (i+1)) + stT259 183 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 182
    simpa using h
  have hprev := st259_p182
  have hstep := st259_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p184 : ((382300168601/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT259 (i+1))
      = (∑ i ∈ Finset.range 183, stT259 (i+1)) + stT259 184 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 183
    simpa using h
  have hprev := st259_p183
  have hstep := st259_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p185 : ((3913859064523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT259 (i+1))
      = (∑ i ∈ Finset.range 184, stT259 (i+1)) + stT259 185 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 184
    simpa using h
  have hprev := st259_p184
  have hstep := st259_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p186 : ((3579743583313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT259 (i+1))
      = (∑ i ∈ Finset.range 185, stT259 (i+1)) + stT259 186 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 185
    simpa using h
  have hprev := st259_p185
  have hstep := st259_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p187 : ((1348535675181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT259 (i+1))
      = (∑ i ∈ Finset.range 186, stT259 (i+1)) + stT259 187 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 186
    simpa using h
  have hprev := st259_p186
  have hstep := st259_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p188 : ((1450582689261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT259 (i+1))
      = (∑ i ∈ Finset.range 187, stT259 (i+1)) + stT259 188 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 187
    simpa using h
  have hprev := st259_p187
  have hstep := st259_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p189 : ((314482278633/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT259 (i+1))
      = (∑ i ∈ Finset.range 188, stT259 (i+1)) + stT259 189 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 188
    simpa using h
  have hprev := st259_p188
  have hstep := st259_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p190 : ((7596919788543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT259 (i+1))
      = (∑ i ∈ Finset.range 189, stT259 (i+1)) + stT259 190 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 189
    simpa using h
  have hprev := st259_p189
  have hstep := st259_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p191 : ((3441442562459/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT259 (i+1))
      = (∑ i ∈ Finset.range 190, stT259 (i+1)) + stT259 191 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 190
    simpa using h
  have hprev := st259_p190
  have hstep := st259_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p192 : ((3421427267467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT259 (i+1))
      = (∑ i ∈ Finset.range 191, stT259 (i+1)) + stT259 192 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 191
    simpa using h
  have hprev := st259_p191
  have hstep := st259_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p193 : ((7534443429339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT259 (i+1))
      = (∑ i ∈ Finset.range 192, stT259 (i+1)) + stT259 193 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 192
    simpa using h
  have hprev := st259_p192
  have hstep := st259_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p194 : ((7886822959403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT259 (i+1))
      = (∑ i ∈ Finset.range 193, stT259 (i+1)) + stT259 194 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 193
    simpa using h
  have hprev := st259_p193
  have hstep := st259_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p195 : ((1840978051457/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT259 (i+1))
      = (∑ i ∈ Finset.range 194, stT259 (i+1)) + stT259 195 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 194
    simpa using h
  have hprev := st259_p194
  have hstep := st259_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p196 : ((3381754197119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT259 (i+1))
      = (∑ i ∈ Finset.range 195, stT259 (i+1)) + stT259 196 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 195
    simpa using h
  have hprev := st259_p195
  have hstep := st259_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p197 : ((3493743081599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT259 (i+1))
      = (∑ i ∈ Finset.range 196, stT259 (i+1)) + stT259 197 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 196
    simpa using h
  have hprev := st259_p196
  have hstep := st259_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p198 : ((3848410974077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT259 (i+1))
      = (∑ i ∈ Finset.range 197, stT259 (i+1)) + stT259 198 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 197
    simpa using h
  have hprev := st259_p197
  have hstep := st259_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p199 : ((61261588233/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT259 (i+1))
      = (∑ i ∈ Finset.range 198, stT259 (i+1)) + stT259 199 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 198
    simpa using h
  have hprev := st259_p198
  have hstep := st259_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p200 : ((3606817958727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT259 (i+1))
      = (∑ i ∈ Finset.range 199, stT259 (i+1)) + stT259 200 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 199
    simpa using h
  have hprev := st259_p199
  have hstep := st259_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p201 : ((336457075443/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT259 (i+1))
      = (∑ i ∈ Finset.range 200, stT259 (i+1)) + stT259 201 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 200
    simpa using h
  have hprev := st259_p200
  have hstep := st259_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p202 : ((7083710070249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT259 (i+1))
      = (∑ i ∈ Finset.range 201, stT259 (i+1)) + stT259 202 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 201
    simpa using h
  have hprev := st259_p201
  have hstep := st259_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p203 : ((7766011176309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT259 (i+1))
      = (∑ i ∈ Finset.range 202, stT259 (i+1)) + stT259 203 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 202
    simpa using h
  have hprev := st259_p202
  have hstep := st259_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p204 : ((7809104793309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT259 (i+1))
      = (∑ i ∈ Finset.range 203, stT259 (i+1)) + stT259 204 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 203
    simpa using h
  have hprev := st259_p203
  have hstep := st259_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p205 : ((447304993311/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT259 (i+1))
      = (∑ i ∈ Finset.range 204, stT259 (i+1)) + stT259 205 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 204
    simpa using h
  have hprev := st259_p204
  have hstep := st259_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p206 : ((840088809287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT259 (i+1))
      = (∑ i ∈ Finset.range 205, stT259 (i+1)) + stT259 206 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 205
    simpa using h
  have hprev := st259_p205
  have hstep := st259_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p207 : ((221885390187/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT259 (i+1))
      = (∑ i ∈ Finset.range 206, stT259 (i+1)) + stT259 207 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 206
    simpa using h
  have hprev := st259_p206
  have hstep := st259_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p208 : ((1942801520121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT259 (i+1))
      = (∑ i ∈ Finset.range 207, stT259 (i+1)) + stT259 208 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 207
    simpa using h
  have hprev := st259_p207
  have hstep := st259_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p209 : ((3910921501927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT259 (i+1))
      = (∑ i ∈ Finset.range 208, stT259 (i+1)) + stT259 209 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 208
    simpa using h
  have hprev := st259_p208
  have hstep := st259_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p210 : ((1797084910919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT259 (i+1))
      = (∑ i ∈ Finset.range 209, stT259 (i+1)) + stT259 210 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 209
    simpa using h
  have hprev := st259_p209
  have hstep := st259_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p211 : ((6719941501653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT259 (i+1))
      = (∑ i ∈ Finset.range 210, stT259 (i+1)) + stT259 211 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 210
    simpa using h
  have hprev := st259_p210
  have hstep := st259_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p212 : ((7034835411039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT259 (i+1))
      = (∑ i ∈ Finset.range 211, stT259 (i+1)) + stT259 212 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 211
    simpa using h
  have hprev := st259_p211
  have hstep := st259_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p213 : ((7714695389151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT259 (i+1))
      = (∑ i ∈ Finset.range 212, stT259 (i+1)) + stT259 213 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 212
    simpa using h
  have hprev := st259_p212
  have hstep := st259_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p214 : ((3936342435383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT259 (i+1))
      = (∑ i ∈ Finset.range 213, stT259 (i+1)) + stT259 214 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 213
    simpa using h
  have hprev := st259_p213
  have hstep := st259_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p215 : ((7308476545221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT259 (i+1))
      = (∑ i ∈ Finset.range 214, stT259 (i+1)) + stT259 215 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 214
    simpa using h
  have hprev := st259_p214
  have hstep := st259_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p216 : ((6748895906653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT259 (i+1))
      = (∑ i ∈ Finset.range 215, stT259 (i+1)) + stT259 216 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 215
    simpa using h
  have hprev := st259_p215
  have hstep := st259_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p217 : ((1380823124757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT259 (i+1))
      = (∑ i ∈ Finset.range 216, stT259 (i+1)) + stT259 217 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 216
    simpa using h
  have hprev := st259_p216
  have hstep := st259_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p218 : ((757383738219/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT259 (i+1))
      = (∑ i ∈ Finset.range 217, stT259 (i+1)) + stT259 218 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 217
    simpa using h
  have hprev := st259_p217
  have hstep := st259_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p219 : ((989766855501/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT259 (i+1))
      = (∑ i ∈ Finset.range 218, stT259 (i+1)) + stT259 219 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 218
    simpa using h
  have hprev := st259_p218
  have hstep := st259_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p220 : ((234769556019/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT259 (i+1))
      = (∑ i ∈ Finset.range 219, stT259 (i+1)) + stT259 220 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 219
    simpa using h
  have hprev := st259_p219
  have hstep := st259_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p221 : ((686068053843/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT259 (i+1))
      = (∑ i ∈ Finset.range 220, stT259 (i+1)) + stT259 221 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 220
    simpa using h
  have hprev := st259_p220
  have hstep := st259_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p222 : ((6758744542113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT259 (i+1))
      = (∑ i ∈ Finset.range 221, stT259 (i+1)) + stT259 222 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 221
    simpa using h
  have hprev := st259_p221
  have hstep := st259_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p223 : ((457898156751/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT259 (i+1))
      = (∑ i ∈ Finset.range 222, stT259 (i+1)) + stT259 223 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 222
    simpa using h
  have hprev := st259_p222
  have hstep := st259_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p224 : ((393895471431/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT259 (i+1))
      = (∑ i ∈ Finset.range 223, stT259 (i+1)) + stT259 224 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 223
    simpa using h
  have hprev := st259_p223
  have hstep := st259_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p225 : ((7756838034751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT259 (i+1))
      = (∑ i ∈ Finset.range 224, stT259 (i+1)) + stT259 225 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 224
    simpa using h
  have hprev := st259_p224
  have hstep := st259_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p226 : ((7110628925127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT259 (i+1))
      = (∑ i ∈ Finset.range 225, stT259 (i+1)) + stT259 226 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 225
    simpa using h
  have hprev := st259_p225
  have hstep := st259_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p227 : ((1340001488823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT259 (i+1))
      = (∑ i ∈ Finset.range 226, stT259 (i+1)) + stT259 227 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 226
    simpa using h
  have hprev := st259_p226
  have hstep := st259_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p228 : ((7000781508409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT259 (i+1))
      = (∑ i ∈ Finset.range 227, stT259 (i+1)) + stT259 228 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 227
    simpa using h
  have hprev := st259_p227
  have hstep := st259_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p229 : ((7661180549797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT259 (i+1))
      = (∑ i ∈ Finset.range 228, stT259 (i+1)) + stT259 229 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 228
    simpa using h
  have hprev := st259_p228
  have hstep := st259_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p230 : ((7922821215037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT259 (i+1))
      = (∑ i ∈ Finset.range 229, stT259 (i+1)) + stT259 230 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 229
    simpa using h
  have hprev := st259_p229
  have hstep := st259_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p231 : ((7491142855549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT259 (i+1))
      = (∑ i ∈ Finset.range 230, stT259 (i+1)) + stT259 231 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 230
    simpa using h
  have hprev := st259_p230
  have hstep := st259_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p232 : ((685724514379/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT259 (i+1))
      = (∑ i ∈ Finset.range 231, stT259 (i+1)) + stT259 232 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 231
    simpa using h
  have hprev := st259_p231
  have hstep := st259_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p233 : ((168284659519/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT259 (i+1))
      = (∑ i ∈ Finset.range 232, stT259 (i+1)) + stT259 233 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 232
    simpa using h
  have hprev := st259_p232
  have hstep := st259_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p234 : ((90623089209/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT259 (i+1))
      = (∑ i ∈ Finset.range 233, stT259 (i+1)) + stT259 234 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 233
    simpa using h
  have hprev := st259_p233
  have hstep := st259_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p235 : ((195932609469/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT259 (i+1))
      = (∑ i ∈ Finset.range 234, stT259 (i+1)) + stT259 235 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 234
    simpa using h
  have hprev := st259_p234
  have hstep := st259_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p236 : ((981397569001/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT259 (i+1))
      = (∑ i ∈ Finset.range 235, stT259 (i+1)) + stT259 236 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 235
    simpa using h
  have hprev := st259_p235
  have hstep := st259_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p237 : ((1820044010877/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT259 (i+1))
      = (∑ i ∈ Finset.range 236, stT259 (i+1)) + stT259 237 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 236
    simpa using h
  have hprev := st259_p236
  have hstep := st259_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p238 : ((42142402887/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT259 (i+1))
      = (∑ i ∈ Finset.range 237, stT259 (i+1)) + stT259 238 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 237
    simpa using h
  have hprev := st259_p237
  have hstep := st259_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p239 : ((1703223378119/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT259 (i+1))
      = (∑ i ∈ Finset.range 238, stT259 (i+1)) + stT259 239 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 238
    simpa using h
  have hprev := st259_p238
  have hstep := st259_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p240 : ((926517420179/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT259 (i+1))
      = (∑ i ∈ Finset.range 239, stT259 (i+1)) + stT259 240 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 239
    simpa using h
  have hprev := st259_p239
  have hstep := st259_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p241 : ((988294557203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT259 (i+1))
      = (∑ i ∈ Finset.range 240, stT259 (i+1)) + stT259 241 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 240
    simpa using h
  have hprev := st259_p240
  have hstep := st259_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p242 : ((1944988480231/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT259 (i+1))
      = (∑ i ∈ Finset.range 241, stT259 (i+1)) + stT259 242 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 241
    simpa using h
  have hprev := st259_p241
  have hstep := st259_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p243 : ((3500002729/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT259 (i+1))
      = (∑ i ∈ Finset.range 242, stT259 (i+1)) + stT259 243 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 242
    simpa using h
  have hprev := st259_p242
  have hstep := st259_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p244 : ((6703406049497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT259 (i+1))
      = (∑ i ∈ Finset.range 243, stT259 (i+1)) + stT259 244 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 243
    simpa using h
  have hprev := st259_p243
  have hstep := st259_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p245 : ((6859749228713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT259 (i+1))
      = (∑ i ∈ Finset.range 244, stT259 (i+1)) + stT259 245 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 244
    simpa using h
  have hprev := st259_p244
  have hstep := st259_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p246 : ((7474445176377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT259 (i+1))
      = (∑ i ∈ Finset.range 245, stT259 (i+1)) + stT259 246 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 245
    simpa using h
  have hprev := st259_p245
  have hstep := st259_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p247 : ((7925774779541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT259 (i+1))
      = (∑ i ∈ Finset.range 246, stT259 (i+1)) + stT259 247 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 246
    simpa using h
  have hprev := st259_p246
  have hstep := st259_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p248 : ((7763811424481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT259 (i+1))
      = (∑ i ∈ Finset.range 247, stT259 (i+1)) + stT259 248 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 247
    simpa using h
  have hprev := st259_p247
  have hstep := st259_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p249 : ((3576565917053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT259 (i+1))
      = (∑ i ∈ Finset.range 248, stT259 (i+1)) + stT259 249 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 248
    simpa using h
  have hprev := st259_p248
  have hstep := st259_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p250 : ((3348955438177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT259 (i+1))
      = (∑ i ∈ Finset.range 249, stT259 (i+1)) + stT259 250 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 249
    simpa using h
  have hprev := st259_p249
  have hstep := st259_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p251 : ((855263156509/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT259 (i+1))
      = (∑ i ∈ Finset.range 250, stT259 (i+1)) + stT259 251 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 250
    simpa using h
  have hprev := st259_p250
  have hstep := st259_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p252 : ((1860474868343/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT259 (i+1))
      = (∑ i ∈ Finset.range 251, stT259 (i+1)) + stT259 252 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 251
    simpa using h
  have hprev := st259_p251
  have hstep := st259_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p253 : ((3958235512677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT259 (i+1))
      = (∑ i ∈ Finset.range 252, stT259 (i+1)) + stT259 253 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 252
    simpa using h
  have hprev := st259_p252
  have hstep := st259_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p254 : ((3906318862053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT259 (i+1))
      = (∑ i ∈ Finset.range 253, stT259 (i+1)) + stT259 254 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 253
    simpa using h
  have hprev := st259_p253
  have hstep := st259_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p255 : ((7232672591081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT259 (i+1))
      = (∑ i ∈ Finset.range 254, stT259 (i+1)) + stT259 255 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 254
    simpa using h
  have hprev := st259_p254
  have hstep := st259_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p256 : ((1681610914029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT259 (i+1))
      = (∑ i ∈ Finset.range 255, stT259 (i+1)) + stT259 256 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 255
    simpa using h
  have hprev := st259_p255
  have hstep := st259_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p257 : ((105740390061/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT259 (i+1))
      = (∑ i ∈ Finset.range 256, stT259 (i+1)) + stT259 257 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 256
    simpa using h
  have hprev := st259_p256
  have hstep := st259_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p258 : ((1828484763747/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT259 (i+1))
      = (∑ i ∈ Finset.range 257, stT259 (i+1)) + stT259 258 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 257
    simpa using h
  have hprev := st259_p257
  have hstep := st259_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p259 : ((3929201849667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT259 (i+1))
      = (∑ i ∈ Finset.range 258, stT259 (i+1)) + stT259 259 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 258
    simpa using h
  have hprev := st259_p258
  have hstep := st259_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p260 : ((3950878136363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT259 (i+1))
      = (∑ i ∈ Finset.range 259, stT259 (i+1)) + stT259 260 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 259
    simpa using h
  have hprev := st259_p259
  have hstep := st259_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p261 : ((3703837508953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT259 (i+1))
      = (∑ i ∈ Finset.range 260, stT259 (i+1)) + stT259 261 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 260
    simpa using h
  have hprev := st259_p260
  have hstep := st259_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p262 : ((34130061289/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT259 (i+1))
      = (∑ i ∈ Finset.range 261, stT259 (i+1)) + stT259 262 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 261
    simpa using h
  have hprev := st259_p261
  have hstep := st259_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p263 : ((3339628132527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT259 (i+1))
      = (∑ i ∈ Finset.range 262, stT259 (i+1)) + stT259 263 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 262
    simpa using h
  have hprev := st259_p262
  have hstep := st259_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p264 : ((1419087257879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT259 (i+1))
      = (∑ i ∈ Finset.range 263, stT259 (i+1)) + stT259 264 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 263
    simpa using h
  have hprev := st259_p263
  have hstep := st259_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p265 : ((77027031403/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT259 (i+1))
      = (∑ i ∈ Finset.range 264, stT259 (i+1)) + stT259 265 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 264
    simpa using h
  have hprev := st259_p264
  have hstep := st259_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p266 : ((497884640829/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT259 (i+1))
      = (∑ i ∈ Finset.range 265, stT259 (i+1)) + stT259 266 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 265
    simpa using h
  have hprev := st259_p265
  have hstep := st259_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p267 : ((957247508163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT259 (i+1))
      = (∑ i ∈ Finset.range 266, stT259 (i+1)) + stT259 267 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 266
    simpa using h
  have hprev := st259_p266
  have hstep := st259_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p268 : ((881101868943/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT259 (i+1))
      = (∑ i ∈ Finset.range 267, stT259 (i+1)) + stT259 268 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 267
    simpa using h
  have hprev := st259_p267
  have hstep := st259_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p269 : ((833110296711/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT259 (i+1))
      = (∑ i ∈ Finset.range 268, stT259 (i+1)) + stT259 269 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 268
    simpa using h
  have hprev := st259_p268
  have hstep := st259_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p270 : ((854125781271/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT259 (i+1))
      = (∑ i ∈ Finset.range 269, stT259 (i+1)) + stT259 270 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 269
    simpa using h
  have hprev := st259_p269
  have hstep := st259_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p271 : ((925874004003/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT259 (i+1))
      = (∑ i ∈ Finset.range 270, stT259 (i+1)) + stT259 271 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 270
    simpa using h
  have hprev := st259_p270
  have hstep := st259_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p272 : ((7900237288083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT259 (i+1))
      = (∑ i ∈ Finset.range 271, stT259 (i+1)) + stT259 272 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 271
    simpa using h
  have hprev := st259_p271
  have hstep := st259_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p273 : ((7900053298771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT259 (i+1))
      = (∑ i ∈ Finset.range 272, stT259 (i+1)) + stT259 273 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 272
    simpa using h
  have hprev := st259_p272
  have hstep := st259_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p274 : ((7409583958761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT259 (i+1))
      = (∑ i ∈ Finset.range 273, stT259 (i+1)) + stT259 274 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 273
    simpa using h
  have hprev := st259_p273
  have hstep := st259_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p275 : ((3418569223011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT259 (i+1))
      = (∑ i ∈ Finset.range 274, stT259 (i+1)) + stT259 275 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 274
    simpa using h
  have hprev := st259_p274
  have hstep := st259_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p276 : ((1663270524103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT259 (i+1))
      = (∑ i ∈ Finset.range 275, stT259 (i+1)) + stT259 276 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 275
    simpa using h
  have hprev := st259_p275
  have hstep := st259_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p277 : ((7005101018969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT259 (i+1))
      = (∑ i ∈ Finset.range 276, stT259 (i+1)) + stT259 277 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 276
    simpa using h
  have hprev := st259_p276
  have hstep := st259_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p278 : ((7604792046569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT259 (i+1))
      = (∑ i ∈ Finset.range 277, stT259 (i+1)) + stT259 278 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 277
    simpa using h
  have hprev := st259_p277
  have hstep := st259_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p279 : ((7968159109581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT259 (i+1))
      = (∑ i ∈ Finset.range 278, stT259 (i+1)) + stT259 279 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 278
    simpa using h
  have hprev := st259_p278
  have hstep := st259_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p280 : ((7806191101821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT259 (i+1))
      = (∑ i ∈ Finset.range 279, stT259 (i+1)) + stT259 280 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 279
    simpa using h
  have hprev := st259_p279
  have hstep := st259_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p281 : ((7250643176421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT259 (i+1))
      = (∑ i ∈ Finset.range 280, stT259 (i+1)) + stT259 281 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 280
    simpa using h
  have hprev := st259_p280
  have hstep := st259_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p282 : ((6742014998969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT259 (i+1))
      = (∑ i ∈ Finset.range 281, stT259 (i+1)) + stT259 282 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 281
    simpa using h
  have hprev := st259_p281
  have hstep := st259_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p283 : ((1669629404857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT259 (i+1))
      = (∑ i ∈ Finset.range 282, stT259 (i+1)) + stT259 283 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 282
    simpa using h
  have hprev := st259_p282
  have hstep := st259_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p284 : ((3553444413689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT259 (i+1))
      = (∑ i ∈ Finset.range 283, stT259 (i+1)) + stT259 284 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 283
    simpa using h
  have hprev := st259_p283
  have hstep := st259_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p285 : ((769288922621/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT259 (i+1))
      = (∑ i ∈ Finset.range 284, stT259 (i+1)) + stT259 285 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 284
    simpa using h
  have hprev := st259_p284
  have hstep := st259_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p286 : ((3992670453241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT259 (i+1))
      = (∑ i ∈ Finset.range 285, stT259 (i+1)) + stT259 286 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 285
    simpa using h
  have hprev := st259_p285
  have hstep := st259_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p287 : ((3881374552987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT259 (i+1))
      = (∑ i ∈ Finset.range 286, stT259 (i+1)) + stT259 287 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 286
    simpa using h
  have hprev := st259_p286
  have hstep := st259_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p288 : ((3598479523831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT259 (i+1))
      = (∑ i ∈ Finset.range 287, stT259 (i+1)) + stT259 288 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 287
    simpa using h
  have hprev := st259_p287
  have hstep := st259_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p289 : ((3358136294243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT259 (i+1))
      = (∑ i ∈ Finset.range 288, stT259 (i+1)) + stT259 289 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 288
    simpa using h
  have hprev := st259_p288
  have hstep := st259_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p290 : ((6680019325609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT259 (i+1))
      = (∑ i ∈ Finset.range 289, stT259 (i+1)) + stT259 290 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 289
    simpa using h
  have hprev := st259_p289
  have hstep := st259_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p291 : ((7112505132469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT259 (i+1))
      = (∑ i ∈ Finset.range 290, stT259 (i+1)) + stT259 291 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 290
    simpa using h
  have hprev := st259_p290
  have hstep := st259_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p292 : ((1922830362371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT259 (i+1))
      = (∑ i ∈ Finset.range 291, stT259 (i+1)) + stT259 292 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 291
    simpa using h
  have hprev := st259_p291
  have hstep := st259_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p293 : ((799053482071/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT259 (i+1))
      = (∑ i ∈ Finset.range 292, stT259 (i+1)) + stT259 293 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 292
    simpa using h
  have hprev := st259_p292
  have hstep := st259_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p294 : ((3896723245139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT259 (i+1))
      = (∑ i ∈ Finset.range 293, stT259 (i+1)) + stT259 294 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 293
    simpa using h
  have hprev := st259_p293
  have hstep := st259_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p295 : ((289833209727/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT259 (i+1))
      = (∑ i ∈ Finset.range 294, stT259 (i+1)) + stT259 295 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 294
    simpa using h
  have hprev := st259_p294
  have hstep := st259_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p296 : ((10790800077/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT259 (i+1))
      = (∑ i ∈ Finset.range 295, stT259 (i+1)) + stT259 296 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 295
    simpa using h
  have hprev := st259_p295
  have hstep := st259_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p297 : ((207734682747/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT259 (i+1))
      = (∑ i ∈ Finset.range 296, stT259 (i+1)) + stT259 297 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 296
    simpa using h
  have hprev := st259_p296
  have hstep := st259_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p298 : ((1755512203631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT259 (i+1))
      = (∑ i ∈ Finset.range 297, stT259 (i+1)) + stT259 298 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 297
    simpa using h
  have hprev := st259_p297
  have hstep := st259_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p299 : ((950041737353/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT259 (i+1))
      = (∑ i ∈ Finset.range 298, stT259 (i+1)) + stT259 299 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 298
    simpa using h
  have hprev := st259_p298
  have hstep := st259_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p300 : ((3987446876387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT259 (i+1))
      = (∑ i ∈ Finset.range 299, stT259 (i+1)) + stT259 300 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 299
    simpa using h
  have hprev := st259_p299
  have hstep := st259_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p301 : ((788537792491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT259 (i+1))
      = (∑ i ∈ Finset.range 300, stT259 (i+1)) + stT259 301 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 300
    simpa using h
  have hprev := st259_p300
  have hstep := st259_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p302 : ((3698273672327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT259 (i+1))
      = (∑ i ∈ Finset.range 301, stT259 (i+1)) + stT259 302 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 301
    simpa using h
  have hprev := st259_p301
  have hstep := st259_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p303 : ((106996091671/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT259 (i+1))
      = (∑ i ∈ Finset.range 302, stT259 (i+1)) + stT259 303 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 302
    simpa using h
  have hprev := st259_p302
  have hstep := st259_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p304 : ((1653846611221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT259 (i+1))
      = (∑ i ∈ Finset.range 303, stT259 (i+1)) + stT259 304 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 303
    simpa using h
  have hprev := st259_p303
  have hstep := st259_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p305 : ((3427933362761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT259 (i+1))
      = (∑ i ∈ Finset.range 304, stT259 (i+1)) + stT259 305 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 304
    simpa using h
  have hprev := st259_p304
  have hstep := st259_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p306 : ((7403709469957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT259 (i+1))
      = (∑ i ∈ Finset.range 305, stT259 (i+1)) + stT259 306 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 305
    simpa using h
  have hprev := st259_p305
  have hstep := st259_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p307 : ((7888591975547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT259 (i+1))
      = (∑ i ∈ Finset.range 306, stT259 (i+1)) + stT259 307 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 306
    simpa using h
  have hprev := st259_p306
  have hstep := st259_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p308 : ((1597332005593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT259 (i+1))
      = (∑ i ∈ Finset.range 307, stT259 (i+1)) + stT259 308 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 307
    simpa using h
  have hprev := st259_p307
  have hstep := st259_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p309 : ((3817457323987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT259 (i+1))
      = (∑ i ∈ Finset.range 308, stT259 (i+1)) + stT259 309 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 308
    simpa using h
  have hprev := st259_p308
  have hstep := st259_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p310 : ((2827286091/4000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT259 (i+1))
      = (∑ i ∈ Finset.range 309, stT259 (i+1)) + stT259 310 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 309
    simpa using h
  have hprev := st259_p309
  have hstep := st259_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p311 : ((1664951285757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT259 (i+1))
      = (∑ i ∈ Finset.range 310, stT259 (i+1)) + stT259 311 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 310
    simpa using h
  have hprev := st259_p310
  have hstep := st259_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p312 : ((166881715909/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT259 (i+1))
      = (∑ i ∈ Finset.range 311, stT259 (i+1)) + stT259 312 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 311
    simpa using h
  have hprev := st259_p311
  have hstep := st259_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p313 : ((7102181773231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT259 (i+1))
      = (∑ i ∈ Finset.range 312, stT259 (i+1)) + stT259 313 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 312
    simpa using h
  have hprev := st259_p312
  have hstep := st259_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p314 : ((1532595872383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT259 (i+1))
      = (∑ i ∈ Finset.range 313, stT259 (i+1)) + stT259 314 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 313
    simpa using h
  have hprev := st259_p313
  have hstep := st259_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p315 : ((7997497512911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT259 (i+1))
      = (∑ i ∈ Finset.range 314, stT259 (i+1)) + stT259 315 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 314
    simpa using h
  have hprev := st259_p314
  have hstep := st259_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p316 : ((7893879720831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT259 (i+1))
      = (∑ i ∈ Finset.range 315, stT259 (i+1)) + stT259 316 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 315
    simpa using h
  have hprev := st259_p315
  have hstep := st259_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p317 : ((7420171748903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT259 (i+1))
      = (∑ i ∈ Finset.range 316, stT259 (i+1)) + stT259 317 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 316
    simpa using h
  have hprev := st259_p316
  have hstep := st259_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p318 : ((6876590927537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT259 (i+1))
      = (∑ i ∈ Finset.range 317, stT259 (i+1)) + stT259 318 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 317
    simpa using h
  have hprev := st259_p317
  have hstep := st259_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p319 : ((1320732649237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT259 (i+1))
      = (∑ i ∈ Finset.range 318, stT259 (i+1)) + stT259 319 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 318
    simpa using h
  have hprev := st259_p318
  have hstep := st259_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p320 : ((6769632860521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT259 (i+1))
      = (∑ i ∈ Finset.range 319, stT259 (i+1)) + stT259 320 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 319
    simpa using h
  have hprev := st259_p319
  have hstep := st259_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p321 : ((3634720551633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT259 (i+1))
      = (∑ i ∈ Finset.range 320, stT259 (i+1)) + stT259 321 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 320
    simpa using h
  have hprev := st259_p320
  have hstep := st259_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p322 : ((974245357463/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT259 (i+1))
      = (∑ i ∈ Finset.range 321, stT259 (i+1)) + stT259 322 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 321
    simpa using h
  have hprev := st259_p321
  have hstep := st259_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p323 : ((501404852387/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT259 (i+1))
      = (∑ i ∈ Finset.range 322, stT259 (i+1)) + stT259 323 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 322
    simpa using h
  have hprev := st259_p322
  have hstep := st259_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p324 : ((1954437285269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT259 (i+1))
      = (∑ i ∈ Finset.range 323, stT259 (i+1)) + stT259 324 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 323
    simpa using h
  have hprev := st259_p323
  have hstep := st259_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p325 : ((1826450014137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT259 (i+1))
      = (∑ i ∈ Finset.range 324, stT259 (i+1)) + stT259 325 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 324
    simpa using h
  have hprev := st259_p324
  have hstep := st259_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p326 : ((6795727835357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT259 (i+1))
      = (∑ i ∈ Finset.range 325, stT259 (i+1)) + stT259 326 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 325
    simpa using h
  have hprev := st259_p325
  have hstep := st259_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p327 : ((6592050009731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT259 (i+1))
      = (∑ i ∈ Finset.range 326, stT259 (i+1)) + stT259 327 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 326
    simpa using h
  have hprev := st259_p326
  have hstep := st259_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p328 : ((1703499449559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT259 (i+1))
      = (∑ i ∈ Finset.range 327, stT259 (i+1)) + stT259 328 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 327
    simpa using h
  have hprev := st259_p327
  have hstep := st259_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p329 : ((732824534579/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT259 (i+1))
      = (∑ i ∈ Finset.range 328, stT259 (i+1)) + stT259 329 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 328
    simpa using h
  have hprev := st259_p328
  have hstep := st259_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p330 : ((3915721114907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT259 (i+1))
      = (∑ i ∈ Finset.range 329, stT259 (i+1)) + stT259 330 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 329
    simpa using h
  have hprev := st259_p329
  have hstep := st259_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p331 : ((8030052949123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT259 (i+1))
      = (∑ i ∈ Finset.range 330, stT259 (i+1)) + stT259 331 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 330
    simpa using h
  have hprev := st259_p330
  have hstep := st259_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p332 : ((7810484633939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT259 (i+1))
      = (∑ i ∈ Finset.range 331, stT259 (i+1)) + stT259 332 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 331
    simpa using h
  have hprev := st259_p331
  have hstep := st259_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p333 : ((7301615715733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT259 (i+1))
      = (∑ i ∈ Finset.range 332, stT259 (i+1)) + stT259 333 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 332
    simpa using h
  have hprev := st259_p332
  have hstep := st259_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p334 : ((6796820685637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT259 (i+1))
      = (∑ i ∈ Finset.range 333, stT259 (i+1)) + stT259 334 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 333
    simpa using h
  have hprev := st259_p333
  have hstep := st259_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p335 : ((3291967316541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT259 (i+1))
      = (∑ i ∈ Finset.range 334, stT259 (i+1)) + stT259 335 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 334
    simpa using h
  have hprev := st259_p334
  have hstep := st259_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p336 : ((3391045744557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT259 (i+1))
      = (∑ i ∈ Finset.range 335, stT259 (i+1)) + stT259 336 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 335
    simpa using h
  have hprev := st259_p335
  have hstep := st259_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p337 : ((3638681820957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT259 (i+1))
      = (∑ i ∈ Finset.range 336, stT259 (i+1)) + stT259 337 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 336
    simpa using h
  have hprev := st259_p336
  have hstep := st259_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p338 : ((3895237700537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT259 (i+1))
      = (∑ i ∈ Finset.range 337, stT259 (i+1)) + stT259 338 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 337
    simpa using h
  have hprev := st259_p337
  have hstep := st259_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p339 : ((2008809756831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT259 (i+1))
      = (∑ i ∈ Finset.range 338, stT259 (i+1)) + stT259 339 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 338
    simpa using h
  have hprev := st259_p338
  have hstep := st259_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p340 : ((787736655297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT259 (i+1))
      = (∑ i ∈ Finset.range 339, stT259 (i+1)) + stT259 340 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 339
    simpa using h
  have hprev := st259_p339
  have hstep := st259_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p341 : ((925750757111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT259 (i+1))
      = (∑ i ∈ Finset.range 340, stT259 (i+1)) + stT259 341 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 340
    simpa using h
  have hprev := st259_p340
  have hstep := st259_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p342 : ((860150464587/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT259 (i+1))
      = (∑ i ∈ Finset.range 341, stT259 (i+1)) + stT259 342 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 341
    simpa using h
  have hprev := st259_p341
  have hstep := st259_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p343 : ((1647336675749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT259 (i+1))
      = (∑ i ∈ Finset.range 342, stT259 (i+1)) + stT259 343 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 342
    simpa using h
  have hprev := st259_p342
  have hstep := st259_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p344 : ((334371777463/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT259 (i+1))
      = (∑ i ∈ Finset.range 343, stT259 (i+1)) + stT259 344 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 343
    simpa using h
  have hprev := st259_p343
  have hstep := st259_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p345 : ((890066614303/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT259 (i+1))
      = (∑ i ∈ Finset.range 344, stT259 (i+1)) + stT259 345 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 344
    simpa using h
  have hprev := st259_p344
  have hstep := st259_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p346 : ((7654640957321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT259 (i+1))
      = (∑ i ∈ Finset.range 345, stT259 (i+1)) + stT259 346 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 345
    simpa using h
  have hprev := st259_p345
  have hstep := st259_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p347 : ((8004403188301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT259 (i+1))
      = (∑ i ∈ Finset.range 346, stT259 (i+1)) + stT259 347 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 346
    simpa using h
  have hprev := st259_p346
  have hstep := st259_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p348 : ((3992634316843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT259 (i+1))
      = (∑ i ∈ Finset.range 347, stT259 (i+1)) + stT259 348 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 347
    simpa using h
  have hprev := st259_p347
  have hstep := st259_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p349 : ((3804610927471/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT259 (i+1))
      = (∑ i ∈ Finset.range 348, stT259 (i+1)) + stT259 349 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 348
    simpa using h
  have hprev := st259_p348
  have hstep := st259_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p350 : ((7075364336077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT259 (i+1))
      = (∑ i ∈ Finset.range 349, stT259 (i+1)) + stT259 350 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 349
    simpa using h
  have hprev := st259_p349
  have hstep := st259_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p351 : ((1665754621127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT259 (i+1))
      = (∑ i ∈ Finset.range 350, stT259 (i+1)) + stT259 351 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 350
    simpa using h
  have hprev := st259_p350
  have hstep := st259_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p352 : ((1646374668407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT259 (i+1))
      = (∑ i ∈ Finset.range 351, stT259 (i+1)) + stT259 352 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 351
    simpa using h
  have hprev := st259_p351
  have hstep := st259_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p353 : ((3440542075479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT259 (i+1))
      = (∑ i ∈ Finset.range 352, stT259 (i+1)) + stT259 353 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 352
    simpa using h
  have hprev := st259_p352
  have hstep := st259_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p354 : ((1849031438547/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT259 (i+1))
      = (∑ i ∈ Finset.range 353, stT259 (i+1)) + stT259 354 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 353
    simpa using h
  have hprev := st259_p353
  have hstep := st259_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p355 : ((1966635286299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT259 (i+1))
      = (∑ i ∈ Finset.range 354, stT259 (i+1)) + stT259 355 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 354
    simpa using h
  have hprev := st259_p354
  have hstep := st259_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p356 : ((503354221191/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT259 (i+1))
      = (∑ i ∈ Finset.range 355, stT259 (i+1)) + stT259 356 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 355
    simpa using h
  have hprev := st259_p355
  have hstep := st259_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p357 : ((122881728753/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT259 (i+1))
      = (∑ i ∈ Finset.range 356, stT259 (i+1)) + stT259 357 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 356
    simpa using h
  have hprev := st259_p356
  have hstep := st259_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p358 : ((1848947597039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT259 (i+1))
      = (∑ i ∈ Finset.range 357, stT259 (i+1)) + stT259 358 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 357
    simpa using h
  have hprev := st259_p357
  have hstep := st259_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p359 : ((860416018387/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT259 (i+1))
      = (∑ i ∈ Finset.range 358, stT259 (i+1)) + stT259 359 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 358
    simpa using h
  have hprev := st259_p358
  have hstep := st259_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p360 : ((6581973740483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT259 (i+1))
      = (∑ i ∈ Finset.range 359, stT259 (i+1)) + stT259 360 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 359
    simpa using h
  have hprev := st259_p359
  have hstep := st259_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p361 : ((6639635759253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT259 (i+1))
      = (∑ i ∈ Finset.range 360, stT259 (i+1)) + stT259 361 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 360
    simpa using h
  have hprev := st259_p360
  have hstep := st259_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p362 : ((7026142662693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT259 (i+1))
      = (∑ i ∈ Finset.range 361, stT259 (i+1)) + stT259 362 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 361
    simpa using h
  have hprev := st259_p361
  have hstep := st259_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p363 : ((755074270633/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT259 (i+1))
      = (∑ i ∈ Finset.range 362, stT259 (i+1)) + stT259 363 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 362
    simpa using h
  have hprev := st259_p362
  have hstep := st259_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p364 : ((3978726393899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT259 (i+1))
      = (∑ i ∈ Finset.range 363, stT259 (i+1)) + stT259 364 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 363
    simpa using h
  have hprev := st259_p363
  have hstep := st259_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p365 : ((8049970420163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT259 (i+1))
      = (∑ i ∈ Finset.range 364, stT259 (i+1)) + stT259 365 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 364
    simpa using h
  have hprev := st259_p364
  have hstep := st259_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p366 : ((389264914307/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT259 (i+1))
      = (∑ i ∈ Finset.range 365, stT259 (i+1)) + stT259 366 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 365
    simpa using h
  have hprev := st259_p365
  have hstep := st259_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p367 : ((455749416519/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT259 (i+1))
      = (∑ i ∈ Finset.range 366, stT259 (i+1)) + stT259 367 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 366
    simpa using h
  have hprev := st259_p366
  have hstep := st259_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p368 : ((6806244490677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT259 (i+1))
      = (∑ i ∈ Finset.range 367, stT259 (i+1)) + stT259 368 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 367
    simpa using h
  have hprev := st259_p367
  have hstep := st259_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p369 : ((6558279222177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT259 (i+1))
      = (∑ i ∈ Finset.range 368, stT259 (i+1)) + stT259 369 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 368
    simpa using h
  have hprev := st259_p368
  have hstep := st259_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p370 : ((3331925379151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT259 (i+1))
      = (∑ i ∈ Finset.range 369, stT259 (i+1)) + stT259 370 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 369
    simpa using h
  have hprev := st259_p369
  have hstep := st259_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p371 : ((3535830967651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT259 (i+1))
      = (∑ i ∈ Finset.range 370, stT259 (i+1)) + stT259 371 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 370
    simpa using h
  have hprev := st259_p370
  have hstep := st259_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p372 : ((7589878216277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT259 (i+1))
      = (∑ i ∈ Finset.range 371, stT259 (i+1)) + stT259 372 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 371
    simpa using h
  have hprev := st259_p371
  have hstep := st259_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p373 : ((7977315385757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT259 (i+1))
      = (∑ i ∈ Finset.range 372, stT259 (i+1)) + stT259 373 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 372
    simpa using h
  have hprev := st259_p372
  have hstep := st259_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p374 : ((4027817467019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT259 (i+1))
      = (∑ i ∈ Finset.range 373, stT259 (i+1)) + stT259 374 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 373
    simpa using h
  have hprev := st259_p373
  have hstep := st259_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p375 : ((3895164115983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT259 (i+1))
      = (∑ i ∈ Finset.range 374, stT259 (i+1)) + stT259 375 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 374
    simpa using h
  have hprev := st259_p374
  have hstep := st259_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p376 : ((3652189972599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT259 (i+1))
      = (∑ i ∈ Finset.range 375, stT259 (i+1)) + stT259 376 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 375
    simpa using h
  have hprev := st259_p375
  have hstep := st259_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p377 : ((6819912072243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT259 (i+1))
      = (∑ i ∈ Finset.range 376, stT259 (i+1)) + stT259 377 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 376
    simpa using h
  have hprev := st259_p376
  have hstep := st259_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p378 : ((1639043232407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT259 (i+1))
      = (∑ i ∈ Finset.range 377, stT259 (i+1)) + stT259 378 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 377
    simpa using h
  have hprev := st259_p377
  have hstep := st259_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p379 : ((3315427341989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT259 (i+1))
      = (∑ i ∈ Finset.range 378, stT259 (i+1)) + stT259 379 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 378
    simpa using h
  have hprev := st259_p378
  have hstep := st259_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p380 : ((3504416593501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT259 (i+1))
      = (∑ i ∈ Finset.range 379, stT259 (i+1)) + stT259 380 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 379
    simpa using h
  have hprev := st259_p379
  have hstep := st259_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p381 : ((7520147635807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT259 (i+1))
      = (∑ i ∈ Finset.range 380, stT259 (i+1)) + stT259 381 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 380
    simpa using h
  have hprev := st259_p380
  have hstep := st259_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p382 : ((7937362619167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT259 (i+1))
      = (∑ i ∈ Finset.range 381, stT259 (i+1)) + stT259 382 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 381
    simpa using h
  have hprev := st259_p381
  have hstep := st259_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p383 : ((1615362922451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT259 (i+1))
      = (∑ i ∈ Finset.range 382, stT259 (i+1)) + stT259 383 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 382
    simpa using h
  have hprev := st259_p382
  have hstep := st259_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p384 : ((7878583283683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT259 (i+1))
      = (∑ i ∈ Finset.range 383, stT259 (i+1)) + stT259 384 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 383
    simpa using h
  have hprev := st259_p383
  have hstep := st259_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p385 : ((7430882998083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT259 (i+1))
      = (∑ i ∈ Finset.range 384, stT259 (i+1)) + stT259 385 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 384
    simpa using h
  have hprev := st259_p384
  have hstep := st259_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p386 : ((3464758530217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT259 (i+1))
      = (∑ i ∈ Finset.range 385, stT259 (i+1)) + stT259 386 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 385
    simpa using h
  have hprev := st259_p385
  have hstep := st259_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p387 : ((3295795053907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT259 (i+1))
      = (∑ i ∈ Finset.range 386, stT259 (i+1)) + stT259 387 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 386
    simpa using h
  have hprev := st259_p386
  have hstep := st259_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p388 : ((820220722917/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT259 (i+1))
      = (∑ i ∈ Finset.range 387, stT259 (i+1)) + stT259 388 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 387
    simpa using h
  have hprev := st259_p387
  have hstep := st259_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p389 : ((856417134227/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT259 (i+1))
      = (∑ i ∈ Finset.range 388, stT259 (i+1)) + stT259 389 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 388
    simpa using h
  have hprev := st259_p388
  have hstep := st259_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p390 : ((916922153299/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT259 (i+1))
      = (∑ i ∈ Finset.range 389, stT259 (i+1)) + stT259 390 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 389
    simpa using h
  have hprev := st259_p389
  have hstep := st259_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p391 : ((7807695860063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT259 (i+1))
      = (∑ i ∈ Finset.range 390, stT259 (i+1)) + stT259 391 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 390
    simpa using h
  have hprev := st259_p390
  have hstep := st259_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p392 : ((8069031778907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT259 (i+1))
      = (∑ i ∈ Finset.range 391, stT259 (i+1)) + stT259 392 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 391
    simpa using h
  have hprev := st259_p391
  have hstep := st259_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p393 : ((8010627905953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT259 (i+1))
      = (∑ i ∈ Finset.range 392, stT259 (i+1)) + stT259 393 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 392
    simpa using h
  have hprev := st259_p392
  have hstep := st259_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p394 : ((59831120291/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT259 (i+1))
      = (∑ i ∈ Finset.range 393, stT259 (i+1)) + stT259 394 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 393
    simpa using h
  have hprev := st259_p393
  have hstep := st259_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p395 : ((7160132649033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT259 (i+1))
      = (∑ i ∈ Finset.range 394, stT259 (i+1)) + stT259 395 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 394
    simpa using h
  have hprev := st259_p394
  have hstep := st259_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p396 : ((6722715990521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT259 (i+1))
      = (∑ i ∈ Finset.range 395, stT259 (i+1)) + stT259 396 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 395
    simpa using h
  have hprev := st259_p395
  have hstep := st259_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p397 : ((6525947569133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT259 (i+1))
      = (∑ i ∈ Finset.range 396, stT259 (i+1)) + stT259 397 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 396
    simpa using h
  have hprev := st259_p396
  have hstep := st259_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p398 : ((6649341767567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT259 (i+1))
      = (∑ i ∈ Finset.range 397, stT259 (i+1)) + stT259 398 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 397
    simpa using h
  have hprev := st259_p397
  have hstep := st259_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p399 : ((7041070098169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT259 (i+1))
      = (∑ i ∈ Finset.range 398, stT259 (i+1)) + stT259 399 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 398
    simpa using h
  have hprev := st259_p398
  have hstep := st259_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p400 : ((7540903598169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT259 (i+1))
      = (∑ i ∈ Finset.range 399, stT259 (i+1)) + stT259 400 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 399
    simpa using h
  have hprev := st259_p399
  have hstep := st259_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p401 : ((7946461829049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT259 (i+1))
      = (∑ i ∈ Finset.range 400, stT259 (i+1)) + stT259 401 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 400
    simpa using h
  have hprev := st259_p400
  have hstep := st259_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p402 : ((8095168825427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT259 (i+1))
      = (∑ i ∈ Finset.range 401, stT259 (i+1)) + stT259 402 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 401
    simpa using h
  have hprev := st259_p401
  have hstep := st259_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p403 : ((7928706220171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT259 (i+1))
      = (∑ i ∈ Finset.range 402, stT259 (i+1)) + stT259 403 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 402
    simpa using h
  have hprev := st259_p402
  have hstep := st259_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p404 : ((7514787327817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT259 (i+1))
      = (∑ i ∈ Finset.range 403, stT259 (i+1)) + stT259 404 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 403
    simpa using h
  have hprev := st259_p403
  have hstep := st259_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p405 : ((7018531787537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT259 (i+1))
      = (∑ i ∈ Finset.range 404, stT259 (i+1)) + stT259 405 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 404
    simpa using h
  have hprev := st259_p404
  have hstep := st259_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p406 : ((6635988921353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT259 (i+1))
      = (∑ i ∈ Finset.range 405, stT259 (i+1)) + stT259 406 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 405
    simpa using h
  have hprev := st259_p405
  have hstep := st259_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p407 : ((6516752616253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT259 (i+1))
      = (∑ i ∈ Finset.range 406, stT259 (i+1)) + stT259 407 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 406
    simpa using h
  have hprev := st259_p406
  have hstep := st259_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p408 : ((67061868539/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT259 (i+1))
      = (∑ i ∈ Finset.range 407, stT259 (i+1)) + stT259 408 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 407
    simpa using h
  have hprev := st259_p407
  have hstep := st259_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p409 : ((22278863651/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT259 (i+1))
      = (∑ i ∈ Finset.range 408, stT259 (i+1)) + stT259 409 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 408
    simpa using h
  have hprev := st259_p408
  have hstep := st259_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p410 : ((238160832573/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT259 (i+1))
      = (∑ i ∈ Finset.range 409, stT259 (i+1)) + stT259 410 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 409
    simpa using h
  have hprev := st259_p409
  have hstep := st259_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p411 : ((1998041314893/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT259 (i+1))
      = (∑ i ∈ Finset.range 410, stT259 (i+1)) + stT259 411 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 410
    simpa using h
  have hprev := st259_p410
  have hstep := st259_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p412 : ((405031557557/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT259 (i+1))
      = (∑ i ∈ Finset.range 411, stT259 (i+1)) + stT259 412 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 411
    simpa using h
  have hprev := st259_p411
  have hstep := st259_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p413 : ((494146531139/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT259 (i+1))
      = (∑ i ∈ Finset.range 412, stT259 (i+1)) + stT259 413 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 412
    simpa using h
  have hprev := st259_p412
  have hstep := st259_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p414 : ((467776493669/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT259 (i+1))
      = (∑ i ∈ Finset.range 413, stT259 (i+1)) + stT259 414 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 413
    simpa using h
  have hprev := st259_p413
  have hstep := st259_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p415 : ((6995343941093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT259 (i+1))
      = (∑ i ∈ Finset.range 414, stT259 (i+1)) + stT259 415 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 414
    simpa using h
  have hprev := st259_p414
  have hstep := st259_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p416 : ((6623374868123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT259 (i+1))
      = (∑ i ∈ Finset.range 415, stT259 (i+1)) + stT259 416 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 415
    simpa using h
  have hprev := st259_p415
  have hstep := st259_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p417 : ((1626815959577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT259 (i+1))
      = (∑ i ∈ Finset.range 416, stT259 (i+1)) + stT259 417 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 416
    simpa using h
  have hprev := st259_p416
  have hstep := st259_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p418 : ((6689127066723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT259 (i+1))
      = (∑ i ∈ Finset.range 417, stT259 (i+1)) + stT259 418 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 417
    simpa using h
  have hprev := st259_p417
  have hstep := st259_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p419 : ((3550080952831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT259 (i+1))
      = (∑ i ∈ Finset.range 418, stT259 (i+1)) + stT259 419 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 418
    simpa using h
  have hprev := st259_p418
  have hstep := st259_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p420 : ((1896890008553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT259 (i+1))
      = (∑ i ∈ Finset.range 419, stT259 (i+1)) + stT259 420 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 419
    simpa using h
  have hprev := st259_p419
  have hstep := st259_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p421 : ((1992955996623/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT259 (i+1))
      = (∑ i ∈ Finset.range 420, stT259 (i+1)) + stT259 421 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 420
    simpa using h
  have hprev := st259_p420
  have hstep := st259_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p422 : ((2028201806289/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT259 (i+1))
      = (∑ i ∈ Finset.range 421, stT259 (i+1)) + stT259 422 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 421
    simpa using h
  have hprev := st259_p421
  have hstep := st259_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p423 : ((1592048119249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT259 (i+1))
      = (∑ i ∈ Finset.range 422, stT259 (i+1)) + stT259 423 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 422
    simpa using h
  have hprev := st259_p422
  have hstep := st259_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p424 : ((7570712173661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT259 (i+1))
      = (∑ i ∈ Finset.range 423, stT259 (i+1)) + stT259 424 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 423
    simpa using h
  have hprev := st259_p423
  have hstep := st259_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p425 : ((7085833717389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT259 (i+1))
      = (∑ i ∈ Finset.range 424, stT259 (i+1)) + stT259 425 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 424
    simpa using h
  have hprev := st259_p424
  have hstep := st259_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p426 : ((6680204766973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT259 (i+1))
      = (∑ i ∈ Finset.range 425, stT259 (i+1)) + stT259 426 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 425
    simpa using h
  have hprev := st259_p425
  have hstep := st259_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p427 : ((6498529652231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT259 (i+1))
      = (∑ i ∈ Finset.range 426, stT259 (i+1)) + stT259 427 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 426
    simpa using h
  have hprev := st259_p426
  have hstep := st259_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p428 : ((1320896106851/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT259 (i+1))
      = (∑ i ∈ Finset.range 427, stT259 (i+1)) + stT259 428 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 427
    simpa using h
  have hprev := st259_p427
  have hstep := st259_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p429 : ((6959260363183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT259 (i+1))
      = (∑ i ∈ Finset.range 428, stT259 (i+1)) + stT259 429 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 428
    simpa using h
  have hprev := st259_p428
  have hstep := st259_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p430 : ((1487321135583/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT259 (i+1))
      = (∑ i ∈ Finset.range 429, stT259 (i+1)) + stT259 430 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 429
    simpa using h
  have hprev := st259_p429
  have hstep := st259_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p431 : ((1967084417283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT259 (i+1))
      = (∑ i ∈ Finset.range 430, stT259 (i+1)) + stT259 431 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 430
    simpa using h
  have hprev := st259_p430
  have hstep := st259_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p432 : ((8103705462507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT259 (i+1))
      = (∑ i ∈ Finset.range 431, stT259 (i+1)) + stT259 432 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 431
    simpa using h
  have hprev := st259_p431
  have hstep := st259_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p433 : ((8061624350457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT259 (i+1))
      = (∑ i ∈ Finset.range 432, stT259 (i+1)) + stT259 433 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 432
    simpa using h
  have hprev := st259_p432
  have hstep := st259_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p434 : ((1551574813157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT259 (i+1))
      = (∑ i ∈ Finset.range 433, stT259 (i+1)) + stT259 434 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 433
    simpa using h
  have hprev := st259_p433
  have hstep := st259_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p435 : ((7298354329793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT259 (i+1))
      = (∑ i ∈ Finset.range 434, stT259 (i+1)) + stT259 435 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 434
    simpa using h
  have hprev := st259_p434
  have hstep := st259_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p436 : ((6841533590441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT259 (i+1))
      = (∑ i ∈ Finset.range 435, stT259 (i+1)) + stT259 436 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 435
    simpa using h
  have hprev := st259_p435
  have hstep := st259_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p437 : ((6543568642511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT259 (i+1))
      = (∑ i ∈ Finset.range 436, stT259 (i+1)) + stT259 437 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 436
    simpa using h
  have hprev := st259_p436
  have hstep := st259_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p438 : ((6505200732449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT259 (i+1))
      = (∑ i ∈ Finset.range 437, stT259 (i+1)) + stT259 438 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 437
    simpa using h
  have hprev := st259_p437
  have hstep := st259_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p439 : ((1347660364039/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT259 (i+1))
      = (∑ i ∈ Finset.range 438, stT259 (i+1)) + stT259 439 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 438
    simpa using h
  have hprev := st259_p438
  have hstep := st259_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p440 : ((7163061513499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT259 (i+1))
      = (∑ i ∈ Finset.range 439, stT259 (i+1)) + stT259 440 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 439
    simpa using h
  have hprev := st259_p439
  have hstep := st259_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p441 : ((7635984373909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT259 (i+1))
      = (∑ i ∈ Finset.range 440, stT259 (i+1)) + stT259 441 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 440
    simpa using h
  have hprev := st259_p440
  have hstep := st259_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p442 : ((7998711069999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT259 (i+1))
      = (∑ i ∈ Finset.range 441, stT259 (i+1)) + stT259 442 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 441
    simpa using h
  have hprev := st259_p441
  have hstep := st259_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p443 : ((8130932920629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT259 (i+1))
      = (∑ i ∈ Finset.range 442, stT259 (i+1)) + stT259 443 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 442
    simpa using h
  have hprev := st259_p442
  have hstep := st259_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p444 : ((998723725497/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT259 (i+1))
      = (∑ i ∈ Finset.range 443, stT259 (i+1)) + stT259 444 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 443
    simpa using h
  have hprev := st259_p443
  have hstep := st259_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p445 : ((3811508073681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT259 (i+1))
      = (∑ i ∈ Finset.range 444, stT259 (i+1)) + stT259 445 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 444
    simpa using h
  have hprev := st259_p444
  have hstep := st259_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p446 : ((894009698751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT259 (i+1))
      = (∑ i ∈ Finset.range 445, stT259 (i+1)) + stT259 446 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 445
    simpa using h
  have hprev := st259_p445
  have hstep := st259_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p447 : ((841435398723/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT259 (i+1))
      = (∑ i ∈ Finset.range 446, stT259 (i+1)) + stT259 447 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 446
    simpa using h
  have hprev := st259_p446
  have hstep := st259_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p448 : ((812253563313/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT259 (i+1))
      = (∑ i ∈ Finset.range 447, stT259 (i+1)) + stT259 448 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 447
    simpa using h
  have hprev := st259_p447
  have hstep := st259_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p449 : ((6526628819691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT259 (i+1))
      = (∑ i ∈ Finset.range 448, stT259 (i+1)) + stT259 449 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 448
    simpa using h
  have hprev := st259_p448
  have hstep := st259_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p450 : ((272277892907/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT259 (i+1))
      = (∑ i ∈ Finset.range 449, stT259 (i+1)) + stT259 450 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 449
    simpa using h
  have hprev := st259_p449
  have hstep := st259_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p451 : ((45298677933/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT259 (i+1))
      = (∑ i ∈ Finset.range 450, stT259 (i+1)) + stT259 451 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 450
    simpa using h
  have hprev := st259_p450
  have hstep := st259_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p452 : ((48170813683/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT259 (i+1))
      = (∑ i ∈ Finset.range 451, stT259 (i+1)) + stT259 452 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 451
    simpa using h
  have hprev := st259_p451
  have hstep := st259_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p453 : ((20097467391/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT259 (i+1))
      = (∑ i ∈ Finset.range 452, stT259 (i+1)) + stT259 453 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 452
    simpa using h
  have hprev := st259_p452
  have hstep := st259_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p454 : ((8138018333307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT259 (i+1))
      = (∑ i ∈ Finset.range 453, stT259 (i+1)) + stT259 454 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 453
    simpa using h
  have hprev := st259_p453
  have hstep := st259_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p455 : ((7974066799547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT259 (i+1))
      = (∑ i ∈ Finset.range 454, stT259 (i+1)) + stT259 455 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 454
    simpa using h
  have hprev := st259_p454
  have hstep := st259_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p456 : ((7599822019323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT259 (i+1))
      = (∑ i ∈ Finset.range 455, stT259 (i+1)) + stT259 456 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 455
    simpa using h
  have hprev := st259_p455
  have hstep := st259_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p457 : ((1426685317329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT259 (i+1))
      = (∑ i ∈ Finset.range 456, stT259 (i+1)) + stT259 457 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 456
    simpa using h
  have hprev := st259_p456
  have hstep := st259_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p458 : ((268831386203/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT259 (i+1))
      = (∑ i ∈ Finset.range 457, stT259 (i+1)) + stT259 458 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 457
    simpa using h
  have hprev := st259_p457
  have hstep := st259_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p459 : ((1622472881111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT259 (i+1))
      = (∑ i ∈ Finset.range 458, stT259 (i+1)) + stT259 459 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 458
    simpa using h
  have hprev := st259_p458
  have hstep := st259_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p460 : ((203481838923/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT259 (i+1))
      = (∑ i ∈ Finset.range 459, stT259 (i+1)) + stT259 460 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 459
    simpa using h
  have hprev := st259_p459
  have hstep := st259_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p461 : ((423606412537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT259 (i+1))
      = (∑ i ∈ Finset.range 460, stT259 (i+1)) + stT259 461 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 460
    simpa using h
  have hprev := st259_p460
  have hstep := st259_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p462 : ((3603014987051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT259 (i+1))
      = (∑ i ∈ Finset.range 461, stT259 (i+1)) + stT259 462 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 461
    simpa using h
  have hprev := st259_p461
  have hstep := st259_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p463 : ((7664876548321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT259 (i+1))
      = (∑ i ∈ Finset.range 462, stT259 (i+1)) + stT259 463 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 462
    simpa using h
  have hprev := st259_p462
  have hstep := st259_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p464 : ((8014515541069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT259 (i+1))
      = (∑ i ∈ Finset.range 463, stT259 (i+1)) + stT259 464 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 463
    simpa using h
  have hprev := st259_p463
  have hstep := st259_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p465 : ((8149455415523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT259 (i+1))
      = (∑ i ∈ Finset.range 464, stT259 (i+1)) + stT259 465 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 464
    simpa using h
  have hprev := st259_p464
  have hstep := st259_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p466 : ((8029859765141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT259 (i+1))
      = (∑ i ∈ Finset.range 465, stT259 (i+1)) + stT259 466 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 465
    simpa using h
  have hprev := st259_p465
  have hstep := st259_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p467 : ((7692682471871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT259 (i+1))
      = (∑ i ∈ Finset.range 466, stT259 (i+1)) + stT259 467 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 466
    simpa using h
  have hprev := st259_p466
  have hstep := st259_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p468 : ((7239670944859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT259 (i+1))
      = (∑ i ∈ Finset.range 467, stT259 (i+1)) + stT259 468 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 467
    simpa using h
  have hprev := st259_p467
  have hstep := st259_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p469 : ((1361250391367/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT259 (i+1))
      = (∑ i ∈ Finset.range 468, stT259 (i+1)) + stT259 469 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 468
    simpa using h
  have hprev := st259_p468
  have hstep := st259_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p470 : ((6520932182407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT259 (i+1))
      = (∑ i ∈ Finset.range 469, stT259 (i+1)) + stT259 470 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 469
    simpa using h
  have hprev := st259_p469
  have hstep := st259_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p471 : ((6467412589231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT259 (i+1))
      = (∑ i ∈ Finset.range 470, stT259 (i+1)) + stT259 471 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 470
    simpa using h
  have hprev := st259_p470
  have hstep := st259_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p472 : ((6660502985731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT259 (i+1))
      = (∑ i ∈ Finset.range 471, stT259 (i+1)) + stT259 472 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 471
    simpa using h
  have hprev := st259_p471
  have hstep := st259_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p473 : ((7042623454131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT259 (i+1))
      = (∑ i ∈ Finset.range 472, stT259 (i+1)) + stT259 473 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 472
    simpa using h
  have hprev := st259_p472
  have hstep := st259_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p474 : ((29302722861/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT259 (i+1))
      = (∑ i ∈ Finset.range 473, stT259 (i+1)) + stT259 474 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 473
    simpa using h
  have hprev := st259_p473
  have hstep := st259_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p475 : ((7903440808543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT259 (i+1))
      = (∑ i ∈ Finset.range 474, stT259 (i+1)) + stT259 475 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 474
    simpa using h
  have hprev := st259_p474
  have hstep := st259_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p476 : ((8132342132539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT259 (i+1))
      = (∑ i ∈ Finset.range 475, stT259 (i+1)) + stT259 476 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 475
    simpa using h
  have hprev := st259_p475
  have hstep := st259_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p477 : ((8122901789497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT259 (i+1))
      = (∑ i ∈ Finset.range 476, stT259 (i+1)) + stT259 477 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 476
    simpa using h
  have hprev := st259_p476
  have hstep := st259_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p478 : ((7878760729197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT259 (i+1))
      = (∑ i ∈ Finset.range 477, stT259 (i+1)) + stT259 478 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 477
    simpa using h
  have hprev := st259_p477
  have hstep := st259_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p479 : ((7470656982861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT259 (i+1))
      = (∑ i ∈ Finset.range 478, stT259 (i+1)) + stT259 479 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 478
    simpa using h
  have hprev := st259_p478
  have hstep := st259_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p480 : ((1403086929237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT259 (i+1))
      = (∑ i ∈ Finset.range 479, stT259 (i+1)) + stT259 480 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 479
    simpa using h
  have hprev := st259_p479
  have hstep := st259_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p481 : ((6642372827517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT259 (i+1))
      = (∑ i ∈ Finset.range 480, stT259 (i+1)) + stT259 481 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 480
    simpa using h
  have hprev := st259_p480
  have hstep := st259_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p482 : ((6456516414973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT259 (i+1))
      = (∑ i ∈ Finset.range 481, stT259 (i+1)) + stT259 482 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 481
    simpa using h
  have hprev := st259_p481
  have hstep := st259_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p483 : ((3254697991599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT259 (i+1))
      = (∑ i ∈ Finset.range 482, stT259 (i+1)) + stT259 483 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 482
    simpa using h
  have hprev := st259_p482
  have hstep := st259_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p484 : ((6785259798243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT259 (i+1))
      = (∑ i ∈ Finset.range 483, stT259 (i+1)) + stT259 484 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 483
    simpa using h
  have hprev := st259_p483
  have hstep := st259_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p485 : ((7206239560831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT259 (i+1))
      = (∑ i ∈ Finset.range 484, stT259 (i+1)) + stT259 485 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 484
    simpa using h
  have hprev := st259_p484
  have hstep := st259_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p486 : ((7654769047249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT259 (i+1))
      = (∑ i ∈ Finset.range 485, stT259 (i+1)) + stT259 486 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 485
    simpa using h
  have hprev := st259_p485
  have hstep := st259_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p487 : ((8006574771873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT259 (i+1))
      = (∑ i ∈ Finset.range 486, stT259 (i+1)) + stT259 487 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 486
    simpa using h
  have hprev := st259_p486
  have hstep := st259_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p488 : ((8165033347739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT259 (i+1))
      = (∑ i ∈ Finset.range 487, stT259 (i+1)) + stT259 488 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 487
    simpa using h
  have hprev := st259_p487
  have hstep := st259_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p489 : ((1617478114767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT259 (i+1))
      = (∑ i ∈ Finset.range 488, stT259 (i+1)) + stT259 489 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 488
    simpa using h
  have hprev := st259_p488
  have hstep := st259_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p490 : ((7795784722097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT259 (i+1))
      = (∑ i ∈ Finset.range 489, stT259 (i+1)) + stT259 490 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 489
    simpa using h
  have hprev := st259_p489
  have hstep := st259_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p491 : ((7370474425441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT259 (i+1))
      = (∑ i ∈ Finset.range 490, stT259 (i+1)) + stT259 491 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 490
    simpa using h
  have hprev := st259_p490
  have hstep := st259_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p492 : ((6927378459051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT259 (i+1))
      = (∑ i ∈ Finset.range 491, stT259 (i+1)) + stT259 492 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 491
    simpa using h
  have hprev := st259_p491
  have hstep := st259_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p493 : ((6586304947761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT259 (i+1))
      = (∑ i ∈ Finset.range 492, stT259 (i+1)) + stT259 493 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 492
    simpa using h
  have hprev := st259_p492
  have hstep := st259_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p494 : ((6438675641277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT259 (i+1))
      = (∑ i ∈ Finset.range 493, stT259 (i+1)) + stT259 494 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 493
    simpa using h
  have hprev := st259_p493
  have hstep := st259_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p495 : ((6523312785873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT259 (i+1))
      = (∑ i ∈ Finset.range 494, stT259 (i+1)) + stT259 495 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 494
    simpa using h
  have hprev := st259_p494
  have hstep := st259_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p496 : ((6816721228749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT259 (i+1))
      = (∑ i ∈ Finset.range 495, stT259 (i+1)) + stT259 496 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 495
    simpa using h
  have hprev := st259_p495
  have hstep := st259_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p497 : ((7240037215669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT259 (i+1))
      = (∑ i ∈ Finset.range 496, stT259 (i+1)) + stT259 497 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 496
    simpa using h
  have hprev := st259_p496
  have hstep := st259_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p498 : ((7680589392409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT259 (i+1))
      = (∑ i ∈ Finset.range 497, stT259 (i+1)) + stT259 498 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 497
    simpa using h
  have hprev := st259_p497
  have hstep := st259_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p499 : ((1604406415259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT259 (i+1))
      = (∑ i ∈ Finset.range 498, stT259 (i+1)) + stT259 499 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 498
    simpa using h
  have hprev := st259_p498
  have hstep := st259_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_p500 : ((255467825789/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT259 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT259 (i+1))
      = (∑ i ∈ Finset.range 499, stT259 (i+1)) + stT259 500 := by
    have h := Finset.sum_range_succ (fun i => stT259 (i+1)) 499
    simpa using h
  have hprev := st259_p499
  have hstep := st259_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st259_s500 :
    |Real.sin (((259 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))
      - ((939689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1527149/5000000) (δ := 1633/125000000) (ψ := -133673/1000000) 259 256
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 259`** (evaluated boundary). -/
theorem station_259_sign : 0 < hardyG ((((259:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 259 500 (by norm_num) (by norm_num)
    ((-133673/1000000 : ℚ) : ℝ)
  have hchain := st259_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT259 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((259 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-133673/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st259_c500
  have hsinb := abs_le.mp st259_s500
  have hbdy_lo : ((-108924980926981/1341625000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((259 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ))) / 2
          - ((((259:ℕ)):ℝ))
            * Real.sin (((259 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-133673/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((259:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((259:ℝ) * Real.log (500:ℝ) - ((-133673/1000000 : ℚ) : ℝ))) / 2
        - ((259:ℝ)) * Real.sin ((259:ℝ) * Real.log (500:ℝ) - ((-133673/1000000 : ℚ) : ℝ))
        ≥ ((-487126883/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((259:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-487126883/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-487126883/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-487126883/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((259:ℕ)):ℝ))+1) * (((((259:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((264838565551/500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((255467825789/312500000000 : ℚ) : ℝ) + ((-108924980926981/1341625000000000 : ℚ) : ℝ)
      - ((264838565551/500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-133673/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((259:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-133673/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((259:ℕ)):ℝ)))).re
      - Real.sin ((-133673/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((259:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((259:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((259:ℕ)):ℝ))
      = (((((259:ℕ)):ℝ)) * (Real.log ((((259:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((259:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_259
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
  have hθwin : |(((-133673/1000000 : ℚ) : ℝ) + ((56:ℤ)) * (2*Real.pi)) - theta ((((259:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((259:ℕ)):ℝ)))
    (φ := ((-133673/1000000 : ℚ) : ℝ) + ((56:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-133673/1000000 : ℚ)) : ℝ) 56).1,
    (cos_sin_shift (((-133673/1000000 : ℚ)) : ℝ) 56).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_259_sign
end AxiomAudit
