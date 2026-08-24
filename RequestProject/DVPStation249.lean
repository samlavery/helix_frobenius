import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 249` (rung-262.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT249 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((249 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((5473/25000 : ℚ) : ℝ))

theorem st249_c1 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((976133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5473/100000) (δ := 1/1000000000) (ψ := 5473/25000) 249 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t1 : ((976083/1000000 : ℚ) : ℝ) ≤ stT249 1 := by
  have hc : ((976083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((976083/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((976083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c2 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-915971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6821793/10000000) (δ := 2519/200000000) (ψ := 5473/25000) 249 27
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t2 : ((-1619311695107/2500000000000 : ℚ) : ℝ) ≤ stT249 2 := by
  have hc : ((-916021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1619311695107/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-916021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c3 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-62491/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3905779/5000000) (δ := 12517/1000000000) (ψ := 5473/25000) 249 44
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t3 : ((-2886480145359/5000000000000 : ℚ) : ℝ) ≤ stT249 3 := by
  have hc : ((-499953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2886480145359/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-499953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c4 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((410733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1517047/10000000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 55
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t4 : ((102677/250000 : ℚ) : ℝ) ≤ stT249 4 := by
  have hc : ((102677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102677/250000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((102677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c5 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-5483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -159273/400000) (δ := 12561/1000000000) (ψ := 5473/25000) 249 64
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t5 : ((-6144155847/625000000000 : ℚ) : ℝ) ≤ stT249 5 := by
  have hc : ((-10991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6144155847/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-10991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c6 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((984381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221217/5000000) (δ := 12611/1000000000) (ψ := 5473/25000) 249 71
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t6 : ((2009256794771/5000000000000 : ℚ) : ℝ) ≤ stT249 6 := by
  have hc : ((984331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2009256794771/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((984331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c7 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((109249/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1268597/10000000) (δ := 6277/500000000) (ψ := 5473/25000) 249 77
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t7 : ((412898704581/1250000000000 : ℚ) : ℝ) ≤ stT249 7 := by
  have hc : ((436971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((412898704581/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((436971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c8 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-4351/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5852077/10000000) (δ := 1249/100000000) (ψ := 5473/25000) 249 82
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t8 : ((-123073706307/500000000000 : ℚ) : ℝ) ≤ stT249 8 := by
  have hc : ((-69621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123073706307/500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-69621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c9 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((484099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316089/5000000) (δ := 12477/1000000000) (ψ := 5473/25000) 249 87
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t9 : ((806789919321/2500000000000 : ℚ) : ℝ) ≤ stT249 9 := by
  have hc : ((242037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((806789919321/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((242037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c10 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((214229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 846809/2500000) (δ := 3137/250000000) (ψ := 5473/25000) 249 91
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t10 : ((677293325583/10000000000000 : ℚ) : ℝ) ≤ stT249 10 := by
  have hc : ((214179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677293325583/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((214179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c11 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((12487/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114017/10000000) (δ := 1573/125000000) (ψ := 5473/25000) 249 95
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t11 : ((301182652683/1000000000000 : ℚ) : ℝ) ≤ stT249 11 := by
  have hc : ((99891/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301182652683/1000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((99891/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c12 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-186399/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6926689/10000000) (δ := 6299/500000000) (ψ := 5473/25000) 249 98
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t12 : ((-16816142299/62500000000 : ℚ) : ℝ) ≤ stT249 12 := by
  have hc : ((-186409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16816142299/62500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-186409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c13 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-379129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6078583/10000000) (δ := 12469/1000000000) (ψ := 5473/25000) 249 102
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t13 : ((-525791999077/2500000000000 : ℚ) : ℝ) ≤ stT249 13 := by
  have hc : ((-189577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-525791999077/2500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-189577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c14 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-951261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7070243/10000000) (δ := 3137/250000000) (ψ := 5473/25000) 249 105
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t14 : ((-2542486145643/10000000000000 : ℚ) : ℝ) ≤ stT249 14 := by
  have hc : ((-951311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2542486145643/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-951311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c15 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-212339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4461911/10000000) (δ := 1247/100000000) (ψ := 5473/25000) 249 107
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t15 : ((-548386061721/10000000000000 : ℚ) : ℝ) ≤ stT249 15 := by
  have hc : ((-212389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548386061721/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-212389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c16 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((2179/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2486763/10000000) (δ := 3153/250000000) (ψ := 5473/25000) 249 110
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t16 : ((5447/40000 : ℚ) : ℝ) ≤ stT249 16 := by
  have hc : ((5447/10000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5447/40000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((5447/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c17 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((36339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959031/2500000) (δ := 12597/1000000000) (ψ := 5473/25000) 249 112
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t17 : ((22003435971/2500000000000 : ℚ) : ℝ) ≤ stT249 17 := by
  have hc : ((36289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22003435971/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((36289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c18 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-124783/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7706661/10000000) (δ := 12627/1000000000) (ψ := 5473/25000) 249 115
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t18 : ((-1176524529611/5000000000000 : ℚ) : ℝ) ≤ stT249 18 := by
  have hc : ((-499157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1176524529611/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-499157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c19 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-144343/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1366439/2500000) (δ := 12461/1000000000) (ψ := 5473/25000) 249 117
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t19 : ((-331174325169/2500000000000 : ℚ) : ℝ) ≤ stT249 19 := by
  have hc : ((-288711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331174325169/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-288711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c20 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-398467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4951603/10000000) (δ := 3139/250000000) (ψ := 5473/25000) 249 119
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t20 : ((-222777777789/2500000000000 : ℚ) : ℝ) ≤ stT249 20 := by
  have hc : ((-398517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222777777789/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-398517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c21 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-184053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599563/1000000) (δ := 1257/100000000) (ψ := 5473/25000) 249 121
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t21 : ((-803327737449/5000000000000 : ℚ) : ℝ) ≤ stT249 21 := by
  have hc : ((-368131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-803327737449/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-368131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c22 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-194289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3627553/5000000) (δ := 6313/500000000) (ψ := 5473/25000) 249 122
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t22 : ((-51780877799/250000000000 : ℚ) : ℝ) ≤ stT249 22 := by
  have hc : ((-194299/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51780877799/250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-194299/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c23 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((5183/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140417/400000) (δ := 12611/1000000000) (ψ := 5473/25000) 249 124
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t23 : ((21608086629/625000000000 : ℚ) : ℝ) ≤ stT249 23 := by
  have hc : ((82903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21608086629/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((82903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c24 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((105583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28243/200000) (δ := 6253/500000000) (ψ := 5473/25000) 249 126
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t24 : ((862030362987/5000000000000 : ℚ) : ℝ) ≤ stT249 24 := by
  have hc : ((422307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((862030362987/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((422307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c25 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-12309/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3708191/5000000) (δ := 12583/1000000000) (ψ := 5473/25000) 249 128
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t25 : ((-196954098477/1000000000000 : ℚ) : ℝ) ≤ stT249 25 := by
  have hc : ((-98477/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196954098477/1000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-98477/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c26 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((869693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1290541/10000000) (δ := 783/62500000) (ψ := 5473/25000) 249 129
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t26 : ((1705509935523/10000000000000 : ℚ) : ℝ) ≤ stT249 26 := by
  have hc : ((869643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1705509935523/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((869643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c27 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-88291/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6632049/10000000) (δ := 12461/1000000000) (ψ := 5473/25000) 249 131
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t27 : ((-21240717537/125000000000 : ℚ) : ℝ) ≤ stT249 27 := by
  have hc : ((-11037/12500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21240717537/125000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-11037/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c28 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((496431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 298881/10000000) (δ := 6227/500000000) (ψ := 5473/25000) 249 132
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t28 : ((234529744933/1250000000000 : ℚ) : ℝ) ≤ stT249 28 := by
  have hc : ((248203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234529744933/1250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((248203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c29 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-210813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1608813/2500000) (δ := 1557/125000000) (ψ := 5473/25000) 249 133
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t29 : ((-391493255527/2500000000000 : ℚ) : ℝ) ≤ stT249 29 := by
  have hc : ((-421651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391493255527/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-421651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c30 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((19999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3876991/10000000) (δ := 3133/250000000) (ψ := 5473/25000) 249 135
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t30 : ((36421707209/10000000000000 : ℚ) : ℝ) ≤ stT249 30 := by
  have hc : ((19949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36421707209/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((19949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c31 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((472907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 826759/10000000) (δ := 6289/500000000) (ψ := 5473/25000) 249 136
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t31 : ((424660567373/2500000000000 : ℚ) : ℝ) ≤ stT249 31 := by
  have hc : ((236441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424660567373/2500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((236441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c32 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-186457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4882361/10000000) (δ := 6259/500000000) (ψ := 5473/25000) 249 137
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t32 : ((-164828362847/2500000000000 : ℚ) : ℝ) ≤ stT249 32 := by
  have hc : ((-93241/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164828362847/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-93241/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c33 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-245487/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1844561/2500000) (δ := 12599/1000000000) (ψ := 5473/25000) 249 139
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t33 : ((-854719766223/5000000000000 : ℚ) : ℝ) ≤ stT249 33 := by
  have hc : ((-490999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-854719766223/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-490999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c34 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-11413/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -900543/2000000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 140
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t34 : ((-19577422683/500000000000 : ℚ) : ℝ) ≤ stT249 34 := by
  have hc : ((-22831/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19577422683/500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-22831/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c35 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((323793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54149/250000) (δ := 12589/1000000000) (ψ := 5473/25000) 249 141
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t35 : ((17102113767/156250000000 : ℚ) : ℝ) ≤ stT249 35 := by
  have hc : ((40471/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17102113767/156250000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((40471/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c36 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((990899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168769/5000000) (δ := 6291/500000000) (ψ := 5473/25000) 249 142
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t36 : ((825707169717/5000000000000 : ℚ) : ℝ) ≤ stT249 36 := by
  have hc : ((990849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((825707169717/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((990849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c37 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((919437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1010377/10000000) (δ := 3157/250000000) (ψ := 5473/25000) 249 143
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t37 : ((1511462114743/10000000000000 : ℚ) : ℝ) ≤ stT249 37 := by
  have hc : ((919387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1511462114743/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((919387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c38 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((723907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237921/1250000) (δ := 2507/200000000) (ψ := 5473/25000) 249 144
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t38 : ((587125479699/5000000000000 : ℚ) : ℝ) ≤ stT249 38 := by
  have hc : ((723857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((587125479699/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((723857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c39 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((292441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2365153/10000000) (δ := 157/12500000) (ψ := 5473/25000) 249 145
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t39 : ((7316252889/78125000000 : ℚ) : ℝ) ≤ stT249 39 := by
  have hc : ((9138/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7316252889/78125000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((9138/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c40 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((113553/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2417521/10000000) (δ := 253/20000000) (ψ := 5473/25000) 249 146
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t40 : ((89763575967/1000000000000 : ℚ) : ℝ) ≤ stT249 40 := by
  have hc : ((113543/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89763575967/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((113543/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c41 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((673191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2080701/10000000) (δ := 12557/1000000000) (ψ := 5473/25000) 249 147
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t41 : ((1051269205917/10000000000000 : ℚ) : ℝ) ≤ stT249 41 := by
  have hc : ((673141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1051269205917/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((673141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c42 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((852839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1373493/10000000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 148
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t42 : ((1315881569037/10000000000000 : ℚ) : ℝ) ≤ stT249 42 := by
  have hc : ((852789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1315881569037/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((852789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c43 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((992159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156633/5000000) (δ := 1579/125000000) (ψ := 5473/25000) 249 149
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t43 : ((302590268673/2000000000000 : ℚ) : ℝ) ≤ stT249 43 := by
  have hc : ((992109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302590268673/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((992109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c44 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((56719/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1083733/10000000) (δ := 6239/500000000) (ψ := 5473/25000) 249 150
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t44 : ((171004715303/1250000000000 : ℚ) : ℝ) ≤ stT249 44 := by
  have hc : ((453727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171004715303/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((453727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c45 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((217413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1401189/5000000) (δ := 6293/500000000) (ψ := 5473/25000) 249 151
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t45 : ((81015670717/1250000000000 : ℚ) : ℝ) ≤ stT249 45 := by
  have hc : ((54347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81015670717/1250000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((54347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c46 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-35283/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1207119/2500000) (δ := 12593/1000000000) (ψ := 5473/25000) 249 152
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t46 : ((-325183331/6250000000 : ℚ) : ℝ) ≤ stT249 46 := by
  have hc : ((-4411/12500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325183331/6250000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-4411/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c47 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-960477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -223399/312500) (δ := 12503/1000000000) (ψ := 5473/25000) 249 153
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t47 : ((-28021454171/200000000000 : ℚ) : ℝ) ≤ stT249 47 := by
  have hc : ((-960527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28021454171/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-960527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c48 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-36283/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2978487/5000000) (δ := 63/5000000) (ψ := 5473/25000) 249 153
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t48 : ((-6546702481/62500000000 : ℚ) : ℝ) ≤ stT249 48 := by
  have hc : ((-72571/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6546702481/62500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-72571/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c49 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((82667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1542231/5000000) (δ := 3149/250000000) (ψ := 5473/25000) 249 154
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t49 : ((236155643439/5000000000000 : ℚ) : ℝ) ≤ stT249 49 := by
  have hc : ((165309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236155643439/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((165309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c50 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((999821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23629/5000000) (δ := 12489/1000000000) (ψ := 5473/25000) 249 155
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t50 : ((1413889145223/10000000000000 : ℚ) : ℝ) ≤ stT249 50 := by
  have hc : ((999771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1413889145223/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((999771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c51 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((198233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3428103/10000000) (δ := 12581/1000000000) (ψ := 5473/25000) 249 156
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t51 : ((6937792281/250000000000 : ℚ) : ℝ) ≤ stT249 51 := by
  have hc : ((198183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6937792281/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((198183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c52 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-474259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7048299/10000000) (δ := 6287/500000000) (ψ := 5473/25000) 249 157
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t52 : ((-164428452821/1250000000000 : ℚ) : ℝ) ≤ stT249 52 := by
  have hc : ((-118571/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164428452821/1250000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-118571/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c53 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-345607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2404603/5000000) (δ := 12529/1000000000) (ψ := 5473/25000) 249 157
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t53 : ((-237398264571/5000000000000 : ℚ) : ℝ) ≤ stT249 53 := by
  have hc : ((-345657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237398264571/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-345657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c54 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((239213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29483/400000) (δ := 1567/125000000) (ψ := 5473/25000) 249 158
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t54 : ((651020997627/5000000000000 : ℚ) : ℝ) ≤ stT249 54 := by
  have hc : ((478401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((651020997627/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((478401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c55 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((150789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1774287/5000000) (δ := 157/12500000) (ψ := 5473/25000) 249 159
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t55 : ((203256316861/10000000000000 : ℚ) : ℝ) ≤ stT249 55 := by
  have hc : ((150739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203256316861/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((150739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c56 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-62327/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7667943/10000000) (δ := 12643/1000000000) (ψ := 5473/25000) 249 159
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t56 : ((-666337458787/5000000000000 : ℚ) : ℝ) ≤ stT249 56 := by
  have hc : ((-498641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-666337458787/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-498641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c57 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((370553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148899/500000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 160
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t57 : ((122685769899/2500000000000 : ℚ) : ℝ) ≤ stT249 57 := by
  have hc : ((370503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122685769899/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((370503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c58 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((723847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -475897/2500000) (δ := 6323/500000000) (ψ := 5473/25000) 249 161
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t58 : ((118798973001/1250000000000 : ℚ) : ℝ) ≤ stT249 58 := by
  have hc : ((723797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118798973001/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((723797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c59 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-469087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6970287/10000000) (δ := 6269/500000000) (ψ := 5473/25000) 249 162
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t59 : ((-7634152771/62500000000 : ℚ) : ℝ) ≤ stT249 59 := by
  have hc : ((-58639/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7634152771/62500000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-58639/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c60 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((173067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3492133/10000000) (δ := 2493/200000000) (ψ := 5473/25000) 249 162
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t60 : ((111681954449/5000000000000 : ℚ) : ℝ) ≤ stT249 60 := by
  have hc : ((173017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111681954449/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((173017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c61 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((717537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1926341/10000000) (δ := 1559/125000000) (ψ := 5473/25000) 249 163
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t61 : ((57415462201/625000000000 : ℚ) : ℝ) ≤ stT249 61 := by
  have hc : ((717487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57415462201/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((717487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c62 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-495333/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7512143/10000000) (δ := 12479/1000000000) (ψ := 5473/25000) 249 164
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t62 : ((-157276412679/1250000000000 : ℚ) : ℝ) ≤ stT249 62 := by
  have hc : ((-247679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157276412679/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-247679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c63 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((139413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1224053/5000000) (δ := 12479/1000000000) (ψ := 5473/25000) 249 164
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t63 : ((351256082681/5000000000000 : ℚ) : ℝ) ≤ stT249 63 := by
  have hc : ((278801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351256082681/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((278801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c64 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((187071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3456541/10000000) (δ := 12617/1000000000) (ψ := 5473/25000) 249 165
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t64 : ((187021/8000000 : ℚ) : ℝ) ≤ stT249 64 := by
  have hc : ((187021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187021/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((187021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c65 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-787741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 774353/1250000) (δ := 6243/500000000) (ψ := 5473/25000) 249 165
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t65 : ((-244283747817/2500000000000 : ℚ) : ℝ) ≤ stT249 65 := by
  have hc : ((-787791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244283747817/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-787791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c66 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((999993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9121/10000000) (δ := 1261/100000000) (ψ := 5473/25000) 249 166
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t66 : ((615421918951/5000000000000 : ℚ) : ℝ) ≤ stT249 66 := by
  have hc : ((999943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615421918951/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((999943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c67 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-825789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6355991/10000000) (δ := 1/80000) (ψ := 5473/25000) 249 167
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t67 : ((-201784675421/2000000000000 : ℚ) : ℝ) ≤ stT249 67 := by
  have hc : ((-825839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201784675421/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-825839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c68 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((205811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2866409/10000000) (δ := 63/5000000) (ψ := 5473/25000) 249 167
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t68 : ((62388038727/1250000000000 : ℚ) : ℝ) ≤ stT249 68 := by
  have hc : ((102893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62388038727/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((102893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c69 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((3461/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1876901/5000000) (δ := 2519/200000000) (ψ := 5473/25000) 249 168
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t69 : ((4163542893/500000000000 : ℚ) : ℝ) ≤ stT249 69 := by
  have hc : ((6917/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4163542893/500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((6917/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c70 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-488587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1300791/2500000) (δ := 2499/200000000) (ψ := 5473/25000) 249 168
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t70 : ((-584033112873/10000000000000 : ℚ) : ℝ) ≤ stT249 70 := by
  have hc : ((-488637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584033112873/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-488637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c71 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((15677/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837443/5000000) (δ := 3147/250000000) (ψ := 5473/25000) 249 169
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t71 : ((4650994739/50000000000 : ℚ) : ℝ) ≤ stT249 71 := by
  have hc : ((3919/5000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4650994739/50000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((3919/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c72 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-946379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3515793/5000000) (δ := 1561/125000000) (ψ := 5473/25000) 249 169
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t72 : ((-69711120853/625000000000 : ℚ) : ℝ) ≤ stT249 72 := by
  have hc : ((-946429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69711120853/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-946429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c73 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((999351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1407/156250) (δ := 12481/1000000000) (ψ := 5473/25000) 249 170
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t73 : ((1169592882711/10000000000000 : ℚ) : ℝ) ≤ stT249 73 := by
  have hc : ((999301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1169592882711/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((999301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c74 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-977993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293141/400000) (δ := 12529/1000000000) (ψ := 5473/25000) 249 171
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t74 : ((-1136952492511/10000000000000 : ℚ) : ℝ) ≤ stT249 74 := by
  have hc : ((-978043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1136952492511/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-978043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c75 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((183349/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205471/2000000) (δ := 12629/1000000000) (ψ := 5473/25000) 249 171
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t75 : ((2117015433/20000000000 : ℚ) : ℝ) ≤ stT249 75 := by
  have hc : ((183339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2117015433/20000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((183339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c76 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-843299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402217/625000) (δ := 12567/1000000000) (ψ := 5473/25000) 249 172
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t76 : ((-967387927571/10000000000000 : ℚ) : ℝ) ≤ stT249 76 := by
  have hc : ((-843349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-967387927571/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-843349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c77 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((194273/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1701911/10000000) (δ := 3159/250000000) (ψ := 5473/25000) 249 172
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t77 : ((88552094841/1000000000000 : ℚ) : ℝ) ≤ stT249 77 := by
  have hc : ((388521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88552094841/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((388521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c78 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-730243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2986843/5000000) (δ := 49/3906250) (ψ := 5473/25000) 249 173
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t78 : ((-413447348727/5000000000000 : ℚ) : ℝ) ≤ stT249 78 := by
  have hc : ((-730293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413447348727/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-730293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c79 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((709127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1956341/10000000) (δ := 12559/1000000000) (ψ := 5473/25000) 249 173
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t79 : ((797773314699/10000000000000 : ℚ) : ℝ) ≤ stT249 79 := by
  have hc : ((709077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((797773314699/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((709077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c80 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-357887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5921319/10000000) (δ := 3113/250000000) (ψ := 5473/25000) 249 174
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t80 : ((-25009861563/312500000000 : ℚ) : ℝ) ≤ stT249 80 := by
  have hc : ((-44739/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25009861563/312500000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-44739/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c81 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((149743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1811687/10000000) (δ := 1569/125000000) (ψ := 5473/25000) 249 174
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t81 : ((166369983363/2000000000000 : ℚ) : ℝ) ≤ stT249 81 := by
  have hc : ((149733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166369983363/2000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((149733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c82 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-50193/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6258139/10000000) (δ := 2509/200000000) (ψ := 5473/25000) 249 175
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t82 : ((-110864767951/1250000000000 : ℚ) : ℝ) ≤ stT249 82 := by
  have hc : ((-401569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110864767951/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-401569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c83 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((435153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1287433/10000000) (δ := 6279/500000000) (ψ := 5473/25000) 249 175
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t83 : ((29850923011/312500000000 : ℚ) : ℝ) ≤ stT249 83 := by
  have hc : ((54391/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29850923011/312500000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((54391/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c84 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-937493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6965377/10000000) (δ := 4993/200000000) (ψ := 5473/25000) 249 176
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t84 : ((-102294379187/1000000000000 : ℚ) : ℝ) ≤ stT249 84 := by
  have hc : ((-937543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102294379187/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-937543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c85 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((987127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12549/312500) (δ := 2493/200000000) (ψ := 5473/25000) 249 176
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t85 : ((267658760551/2500000000000 : ℚ) : ℝ) ≤ stT249 85 := by
  have hc : ((987077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267658760551/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((987077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c86 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-249411/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 960291/1250000) (δ := 2493/200000000) (ψ := 5473/25000) 249 176
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t86 : ((-67240085977/625000000000 : ℚ) : ℝ) ≤ stT249 86 := by
  have hc : ((-498847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67240085977/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-498847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c87 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((472763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33159/400000) (δ := 1559/125000000) (ψ := 5473/25000) 249 177
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t87 : ((15838377583/156250000000 : ℚ) : ℝ) ≤ stT249 87 := by
  have hc : ((236369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15838377583/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((236369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c88 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-161907/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6285391/10000000) (δ := 3143/250000000) (ψ := 5473/25000) 249 177
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t88 : ((-43151042417/500000000000 : ℚ) : ℝ) ≤ stT249 88 := by
  have hc : ((-161917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43151042417/500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-161917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c89 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((288619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1194317/5000000) (δ := 3131/250000000) (ψ := 5473/25000) 249 178
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t89 : ((152954387109/2500000000000 : ℚ) : ℝ) ≤ stT249 89 := by
  have hc : ((144297/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152954387109/2500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((144297/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c90 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-126559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 913349/2000000) (δ := 789/62500000) (ψ := 5473/25000) 249 178
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t90 : ((-16678913539/625000000000 : ℚ) : ℝ) ≤ stT249 90 := by
  have hc : ((-15823/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16678913539/625000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-15823/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c91 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-1071/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2131343/5000000) (δ := 24987/1000000000) (ψ := 5473/25000) 249 179
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t91 : ((-1123132549/80000000000 : ℚ) : ℝ) ≤ stT249 91 := by
  have hc : ((-5357/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1123132549/80000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-5357/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c92 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((10531/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2540647/10000000) (δ := 1577/125000000) (ψ := 5473/25000) 249 179
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t92 : ((274457079/5000000000 : ℚ) : ℝ) ≤ stT249 92 := by
  have hc : ((1053/2000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274457079/5000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((1053/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c93 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-843741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6437531/10000000) (δ := 12609/1000000000) (ψ := 5473/25000) 249 180
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t93 : ((-109371345629/1250000000000 : ℚ) : ℝ) ≤ stT249 93 := by
  have hc : ((-843791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109371345629/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-843791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c94 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((24903/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110147/5000000) (δ := 6297/500000000) (ψ := 5473/25000) 249 180
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t94 : ((102736751547/1000000000000 : ℚ) : ℝ) ≤ stT249 94 := by
  have hc : ((99607/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102736751547/1000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((99607/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c95 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-456843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6807651/10000000) (δ := 6247/500000000) (ψ := 5473/25000) 249 180
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t95 : ((-117184243443/1250000000000 : ℚ) : ℝ) ≤ stT249 95 := by
  have hc : ((-114217/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117184243443/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-114217/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c96 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((579427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297741/1250000) (δ := 12501/1000000000) (ψ := 5473/25000) 249 181
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t96 : ((29566187687/500000000000 : ℚ) : ℝ) ≤ stT249 96 := by
  have hc : ((579377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29566187687/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((579377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c97 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-56739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 813783/2000000) (δ := 12501/1000000000) (ψ := 5473/25000) 249 181
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t97 : ((-57660540783/10000000000000 : ℚ) : ℝ) ≤ stT249 97 := by
  have hc : ((-56789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57660540783/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-56789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c98 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-506357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5254377/10000000) (δ := 3127/250000000) (ψ := 5473/25000) 249 182
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t98 : ((-511548550271/10000000000000 : ℚ) : ℝ) ≤ stT249 98 := by
  have hc : ((-506407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-511548550271/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-506407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c99 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((182109/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266373/2500000) (δ := 3127/250000000) (ψ := 5473/25000) 249 182
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t99 : ((183016232663/2000000000000 : ℚ) : ℝ) ≤ stT249 99 := by
  have hc : ((182099/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183016232663/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((182099/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c100 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-244357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1830451/2500000) (δ := 197/15625000) (ψ := 5473/25000) 249 182
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t100 : ((-488739/5000000 : ℚ) : ℝ) ≤ stT249 100 := by
  have hc : ((-488739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488739/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-488739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c101 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((639603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -548009/2500000) (δ := 3147/250000000) (ψ := 5473/25000) 249 183
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t101 : ((636378898461/10000000000000 : ℚ) : ℝ) ≤ stT249 101 := by
  have hc : ((639553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((636378898461/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((639553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c102 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-1403/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3941021/10000000) (δ := 1561/125000000) (ψ := 5473/25000) 249 183
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t102 : ((-700777247/1250000000000 : ℚ) : ℝ) ≤ stT249 102 := by
  have hc : ((-2831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-700777247/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-2831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c103 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-649337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569377/1000000) (δ := 39/3125000) (ψ := 5473/25000) 249 184
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t103 : ((-63986049271/1000000000000 : ℚ) : ℝ) ≤ stT249 103 := by
  have hc : ((-649387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63986049271/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-649387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c104 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((49589/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320763/10000000) (δ := 12523/1000000000) (ψ := 5473/25000) 249 184
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t104 : ((4862353017/50000000000 : ℚ) : ℝ) ≤ stT249 104 := by
  have hc : ((99173/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4862353017/50000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((99173/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c105 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-12621/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6277777/10000000) (δ := 12623/1000000000) (ψ := 5473/25000) 249 184
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t105 : ((-394163486197/5000000000000 : ℚ) : ℝ) ≤ stT249 105 := by
  have hc : ((-403897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394163486197/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-403897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c106 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((633/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110303/312500) (δ := 12473/1000000000) (ψ := 5473/25000) 249 185
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t106 : ((153657287/10000000000 : ℚ) : ℝ) ≤ stT249 106 := by
  have hc : ((791/5000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153657287/10000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((791/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c107 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((60089/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 463091/2000000) (δ := 1263/100000000) (ψ := 5473/25000) 249 185
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t107 : ((907583841/15625000000 : ℚ) : ℝ) ≤ stT249 107 := by
  have hc : ((15021/25000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((907583841/15625000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((15021/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c108 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-198983/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1520353/2000000) (δ := 6283/500000000) (ψ := 5473/25000) 249 186
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t108 : ((-191481213243/2000000000000 : ℚ) : ℝ) ≤ stT249 108 := by
  have hc : ((-198993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191481213243/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-198993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c109 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((183641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1864431/10000000) (δ := 12537/1000000000) (ψ := 5473/25000) 249 186
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t109 : ((175884151641/2500000000000 : ℚ) : ℝ) ≤ stT249 109 := by
  have hc : ((367257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175884151641/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((367257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c110 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((42563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 76411/200000) (δ := 6233/500000000) (ψ := 5473/25000) 249 186
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t110 : ((20267265003/5000000000000 : ℚ) : ℝ) ≤ stT249 110 := by
  have hc : ((42513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20267265003/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((42513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c111 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-50129/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125077/200000) (δ := 3161/250000000) (ψ := 5473/25000) 249 187
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t111 : ((-190333230003/2500000000000 : ℚ) : ℝ) ≤ stT249 111 := by
  have hc : ((-401057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190333230003/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-401057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c112 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((964207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670897/10000000) (δ := 12459/1000000000) (ψ := 5473/25000) 249 187
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t112 : ((911042555027/10000000000000 : ℚ) : ℝ) ≤ stT249 112 := by
  have hc : ((964157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((911042555027/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((964157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c113 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-182767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2431253/5000000) (δ := 3161/250000000) (ψ := 5473/25000) 249 187
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t113 : ((-21494534129/625000000000 : ℚ) : ℝ) ≤ stT249 113 := by
  have hc : ((-22849/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21494534129/625000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-22849/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c114 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-108523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5360859/10000000) (δ := 12551/1000000000) (ψ := 5473/25000) 249 188
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t114 : ((-50825244169/1000000000000 : ℚ) : ℝ) ≤ stT249 114 := by
  have hc : ((-108533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50825244169/1000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-108533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c115 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((49977/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75869/10000000) (δ := 3113/250000000) (ψ := 5473/25000) 249 188
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t115 : ((11650355287/125000000000 : ℚ) : ℝ) ≤ stT249 115 := by
  have hc : ((99949/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11650355287/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((99949/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c116 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-1804/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2732737/5000000) (δ := 3113/250000000) (ψ := 5473/25000) 249 188
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t116 : ((-53603762641/1000000000000 : ℚ) : ℝ) ≤ stT249 116 := by
  have hc : ((-57733/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53603762641/1000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-57733/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c117 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-379109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2449537/5000000) (δ := 2509/200000000) (ψ := 5473/25000) 249 189
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t117 : ((-350532874659/10000000000000 : ℚ) : ℝ) ≤ stT249 117 := by
  have hc : ((-379159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350532874659/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-379159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c118 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((987301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398837/10000000) (δ := 6229/500000000) (ψ := 5473/25000) 249 189
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t118 : ((454418801037/5000000000000 : ℚ) : ℝ) ≤ stT249 118 := by
  have hc : ((987251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454418801037/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((987251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c119 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-636537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565199/1000000) (δ := 6229/500000000) (ψ := 5473/25000) 249 189
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t119 : ((-583558666313/10000000000000 : ℚ) : ℝ) ≤ stT249 119 := by
  have hc : ((-636587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583558666313/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-636587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c120 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-89911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4846707/10000000) (δ := 12637/1000000000) (ψ := 5473/25000) 249 190
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t120 : ((-164177110737/5000000000000 : ℚ) : ℝ) ≤ stT249 120 := by
  have hc : ((-179847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164177110737/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-179847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c121 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((198371/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4989/156250) (δ := 12637/1000000000) (ψ := 5473/25000) 249 190
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t121 : ((18032800149/200000000000 : ℚ) : ℝ) ≤ stT249 121 := by
  have hc : ((198361/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18032800149/200000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((198361/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c122 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-113969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5442783/10000000) (δ := 6283/500000000) (ψ := 5473/25000) 249 190
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t122 : ((-51595899741/1000000000000 : ℚ) : ℝ) ≤ stT249 122 := by
  have hc : ((-113979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51595899741/1000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-113979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c123 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-240859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2591763/5000000) (δ := 12573/1000000000) (ψ := 5473/25000) 249 191
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t123 : ((-5429946907/125000000000 : ℚ) : ℝ) ≤ stT249 123 := by
  have hc : ((-60221/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5429946907/125000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-60221/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c124 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((249591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143019/10000000) (δ := 12573/1000000000) (ψ := 5473/25000) 249 191
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t124 : ((224127982041/2500000000000 : ℚ) : ℝ) ≤ stT249 124 := by
  have hc : ((499157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224127982041/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((499157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c125 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-90873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194281/400000) (δ := 1253/100000000) (ψ := 5473/25000) 249 191
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t125 : ((-40645267997/1250000000000 : ℚ) : ℝ) ≤ stT249 125 := by
  have hc : ((-181771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40645267997/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-181771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c126 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-707177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2945367/5000000) (δ := 12623/1000000000) (ψ := 5473/25000) 249 192
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t126 : ((-630048024717/10000000000000 : ℚ) : ℝ) ≤ stT249 126 := by
  have hc : ((-707227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-630048024717/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-707227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c127 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((14464/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -969809/10000000) (δ := 12523/1000000000) (ψ := 5473/25000) 249 192
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t127 : ((102672191497/1250000000000 : ℚ) : ℝ) ≤ stT249 127 := by
  have hc : ((462823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102672191497/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((462823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c128 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((5763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3912583/10000000) (δ := 12523/1000000000) (ψ := 5473/25000) 249 192
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t128 : ((5049623579/10000000000000 : ℚ) : ℝ) ≤ stT249 128 := by
  have hc : ((5713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5049623579/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((5713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c129 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-935471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6950961/10000000) (δ := 1577/125000000) (ψ := 5473/25000) 249 193
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t129 : ((-823680399971/10000000000000 : ℚ) : ℝ) ≤ stT249 129 := by
  have hc : ((-935521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-823680399971/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-935521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c130 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((2617/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134001/625000) (δ := 1577/125000000) (ψ := 5473/25000) 249 193
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t130 : ((1434428359/25000000000 : ℚ) : ℝ) ≤ stT249 130 := by
  have hc : ((3271/5000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1434428359/25000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((3271/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c131 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((19887/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131307/500000) (δ := 12587/1000000000) (ψ := 5473/25000) 249 193
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t131 : ((434340101/10000000000 : ℚ) : ℝ) ≤ stT249 131 := by
  have hc : ((3977/8000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434340101/10000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((3977/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c132 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-490271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7360003/10000000) (δ := 3129/250000000) (ψ := 5473/25000) 249 193
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t132 : ((-53343530643/625000000000 : ℚ) : ℝ) ≤ stT249 132 := by
  have hc : ((-61287/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53343530643/625000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-61287/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c133 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((55319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -912457/2500000) (δ := 6247/500000000) (ψ := 5473/25000) 249 194
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t133 : ((23972962523/2500000000000 : ℚ) : ℝ) ≤ stT249 133 := by
  have hc : ((27647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23972962523/2500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((27647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c134 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((919007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 506551/5000000) (δ := 12547/500000000) (ψ := 5473/25000) 249 194
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t134 : ((198464386419/2500000000000 : ℚ) : ℝ) ≤ stT249 134 := by
  have hc : ((918957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198464386419/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((918957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c135 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-633251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2820679/5000000) (δ := 6247/500000000) (ψ := 5473/25000) 249 194
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t135 : ((-545058738563/10000000000000 : ℚ) : ℝ) ≤ stT249 135 := by
  have hc : ((-633301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-545058738563/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-633301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c136 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-57957/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5472493/10000000) (δ := 6251/500000000) (ψ := 5473/25000) 249 195
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t136 : ((-24851004633/500000000000 : ℚ) : ℝ) ≤ stT249 136 := by
  have hc : ((-28981/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24851004633/500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-28981/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c137 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((233549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227999/2500000) (δ := 12501/1000000000) (ψ := 5473/25000) 249 195
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t137 : ((399047087061/5000000000000 : ℚ) : ℝ) ≤ stT249 137 := by
  have hc : ((467073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399047087061/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((467073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c138 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((124369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180763/500000) (δ := 6251/500000000) (ψ := 5473/25000) 249 195
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t138 : ((13228411833/1250000000000 : ℚ) : ℝ) ≤ stT249 138 := by
  have hc : ((124319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13228411833/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((124319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c139 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-198953/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7598067/10000000) (δ := 6297/500000000) (ψ := 5473/25000) 249 196
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t139 : ((-168758228007/2000000000000 : ℚ) : ℝ) ≤ stT249 139 := by
  have hc : ((-198963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168758228007/2000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-198963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c140 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((311267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125427/400000) (δ := 12609/1000000000) (ψ := 5473/25000) 249 196
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t140 : ((131513146209/5000000000000 : ℚ) : ℝ) ≤ stT249 140 := by
  have hc : ((311217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131513146209/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((311217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c141 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((86883/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647453/5000000) (δ := 6247/500000000) (ψ := 5473/25000) 249 196
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t141 : ((36582197289/500000000000 : ℚ) : ℝ) ≤ stT249 141 := by
  have hc : ((43439/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36582197289/500000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((43439/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c142 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-649479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2847119/5000000) (δ := 6247/500000000) (ψ := 5473/25000) 249 196
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t142 : ((-272536522639/5000000000000 : ℚ) : ℝ) ≤ stT249 142 := by
  have hc : ((-649529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272536522639/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-649529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c143 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-634461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5645269/10000000) (δ := 3129/250000000) (ψ := 5473/25000) 249 197
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t143 : ((-530605382173/10000000000000 : ℚ) : ℝ) ≤ stT249 143 := by
  have hc : ((-634511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530605382173/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-634511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c144 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((866361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326829/2500000) (δ := 12587/1000000000) (ψ := 5473/25000) 249 197
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t144 : ((721925544563/10000000000000 : ℚ) : ℝ) ≤ stT249 144 := by
  have hc : ((866311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((721925544563/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((866311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c145 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((181049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375087/1250000) (δ := 1577/125000000) (ψ := 5473/25000) 249 197
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t145 : ((2348939139/78125000000 : ℚ) : ℝ) ≤ stT249 145 := by
  have hc : ((5657/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2348939139/78125000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((5657/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c146 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-38947/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1819769/2500000) (δ := 3129/250000000) (ψ := 5473/25000) 249 197
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t146 : ((-16117213047/200000000000 : ℚ) : ℝ) ≤ stT249 146 := by
  have hc : ((-38949/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16117213047/200000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-38949/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c147 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-100937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -835953/2000000) (δ := 629/50000000) (ψ := 5473/25000) 249 198
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t147 : ((-83292764769/10000000000000 : ℚ) : ℝ) ≤ stT249 147 := by
  have hc : ((-100987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83292764769/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-100987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c148 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((249967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40599/10000000) (δ := 12623/1000000000) (ψ := 5473/25000) 249 198
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t148 : ((205461099273/2500000000000 : ℚ) : ℝ) ≤ stT249 148 := by
  have hc : ((499909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((205461099273/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((499909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c149 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-12193/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33067/78125) (δ := 12523/1000000000) (ψ := 5473/25000) 249 198
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t149 : ((-156140499/15625000000 : ℚ) : ℝ) ≤ stT249 149 := by
  have hc : ((-6099/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156140499/15625000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-6099/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c150 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-976553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7311547/10000000) (δ := 1253/100000000) (ψ := 5473/25000) 249 199
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t150 : ((-797393419691/10000000000000 : ℚ) : ℝ) ≤ stT249 150 := by
  have hc : ((-976603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-797393419691/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-976603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c151 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((74043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -793821/2500000) (δ := 12573/1000000000) (ψ := 5473/25000) 249 199
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t151 : ((30122566267/1250000000000 : ℚ) : ℝ) ≤ stT249 151 := by
  have hc : ((148061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30122566267/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((148061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c152 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((93107/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233413/2500000) (δ := 12473/1000000000) (ψ := 5473/25000) 249 199
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t152 : ((37757841957/500000000000 : ℚ) : ℝ) ≤ stT249 152 := by
  have hc : ((46551/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37757841957/500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((46551/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c153 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-16873/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2507817/5000000) (δ := 1263/100000000) (ψ := 5473/25000) 249 199
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t153 : ((-21828231/640000000 : ℚ) : ℝ) ≤ stT249 153 := by
  have hc : ((-27/64 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21828231/640000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-27/64 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c154 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-55239/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6636929/10000000) (δ := 6233/500000000) (ψ := 5473/25000) 249 200
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t154 : ((-356122999151/5000000000000 : ℚ) : ℝ) ≤ stT249 154 := by
  have hc : ((-441937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356122999151/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-441937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c155 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((62941/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1303899/5000000) (δ := 6283/500000000) (ψ := 5473/25000) 249 200
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t155 : ((202201547841/5000000000000 : ℚ) : ℝ) ≤ stT249 155 := by
  have hc : ((251739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202201547841/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((251739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c156 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((848223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697719/5000000) (δ := 12637/1000000000) (ψ := 5473/25000) 249 200
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t156 : ((1061064423/15625000000 : ℚ) : ℝ) ≤ stT249 156 := by
  have hc : ((848173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1061064423/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((848173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c157 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-546717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167909/312500) (δ := 6233/500000000) (ψ := 5473/25000) 249 200
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t157 : ((-436367634729/10000000000000 : ℚ) : ℝ) ≤ stT249 157 := by
  have hc : ((-546767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-436367634729/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-546767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c158 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-415861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3191249/5000000) (δ := 2509/200000000) (ψ := 5473/25000) 249 201
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t158 : ((-82715358597/1250000000000 : ℚ) : ℝ) ≤ stT249 158 := by
  have hc : ((-207943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82715358597/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-207943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c159 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((555353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2455021/10000000) (δ := 2509/200000000) (ψ := 5473/25000) 249 201
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t159 : ((440383599453/10000000000000 : ℚ) : ℝ) ≤ stT249 159 := by
  have hc : ((555303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440383599453/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((555303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c160 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((836943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289561/2000000) (δ := 2509/200000000) (ψ := 5473/25000) 249 201
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t160 : ((661621662117/10000000000000 : ℚ) : ℝ) ≤ stT249 160 := by
  have hc : ((836893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661621662117/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((836893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c161 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-530949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5326291/10000000) (δ := 6229/500000000) (ψ := 5473/25000) 249 201
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t161 : ((-418486152889/10000000000000 : ℚ) : ℝ) ≤ stT249 161 := by
  have hc : ((-530999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-418486152889/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-530999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c162 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-862437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -407947/625000) (δ := 1569/125000000) (ψ := 5473/25000) 249 202
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t162 : ((-27105378949/400000000000 : ℚ) : ℝ) ≤ stT249 162 := by
  have hc : ((-862487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27105378949/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-862487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c163 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((59077/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53927/200000) (δ := 12651/1000000000) (ψ := 5473/25000) 249 202
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t163 : ((9253551129/250000000000 : ℚ) : ℝ) ≤ stT249 163 := by
  have hc : ((236283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9253551129/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((236283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c164 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((902871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222197/2000000) (δ := 3113/250000000) (ψ := 5473/25000) 249 202
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t164 : ((176246007157/2500000000000 : ℚ) : ℝ) ≤ stT249 164 := by
  have hc : ((902821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176246007157/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((902821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c165 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-377661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2447581/5000000) (δ := 12651/1000000000) (ψ := 5473/25000) 249 202
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t165 : ((-294047635789/10000000000000 : ℚ) : ℝ) ≤ stT249 165 := by
  have hc : ((-377711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294047635789/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-377711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c166 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-948919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7051469/10000000) (δ := 12459/1000000000) (ψ := 5473/25000) 249 203
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t166 : ((-736543238319/10000000000000 : ℚ) : ℝ) ≤ stT249 166 := by
  have hc : ((-948969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-736543238319/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-948969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c167 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((121631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -103521/312500) (δ := 49/3906250) (ψ := 5473/25000) 249 203
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t167 : ((47050759869/2500000000000 : ℚ) : ℝ) ≤ stT249 167 := by
  have hc : ((60803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47050759869/2500000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((60803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c168 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((986989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80743/2000000) (δ := 3161/250000000) (ψ := 5473/25000) 249 203
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t168 : ((190359807381/2500000000000 : ℚ) : ℝ) ≤ stT249 168 := by
  have hc : ((986939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190359807381/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((986939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c169 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-68401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 256133/625000) (δ := 3161/250000000) (ψ := 5473/25000) 249 203
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t169 : ((-52654631181/10000000000000 : ℚ) : ℝ) ≤ stT249 169 := by
  have hc : ((-68451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52654631181/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-68451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c170 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-199889/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1942673/2500000) (δ := 12559/1000000000) (ψ := 5473/25000) 249 203
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t170 : ((-30663107307/400000000000 : ℚ) : ℝ) ≤ stT249 170 := by
  have hc : ((-199899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30663107307/400000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-199899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c171 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-17901/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4286247/10000000) (δ := 12537/1000000000) (ψ := 5473/25000) 249 204
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t171 : ((-684701611/62500000000 : ℚ) : ℝ) ≤ stT249 171 := by
  have hc : ((-71629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-684701611/62500000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-71629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c172 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((965717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5129/78125) (δ := 12637/1000000000) (ψ := 5473/25000) 249 204
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t172 : ((184078340541/2500000000000 : ℚ) : ℝ) ≤ stT249 172 := by
  have hc : ((965667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184078340541/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((965667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c173 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((380117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2952183/10000000) (δ := 12537/1000000000) (ψ := 5473/25000) 249 204
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t173 : ((57791847819/2000000000000 : ℚ) : ℝ) ≤ stT249 173 := by
  have hc : ((380067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57791847819/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((380067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c174 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-216261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3270043/5000000) (δ := 12637/1000000000) (ψ := 5473/25000) 249 204
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t174 : ((-327913448153/5000000000000 : ℚ) : ℝ) ≤ stT249 174 := by
  have hc : ((-432547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327913448153/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-432547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c175 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-620523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1400129/2500000) (δ := 12473/1000000000) (ψ := 5473/25000) 249 205
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t175 : ((-469109127317/10000000000000 : ℚ) : ℝ) ≤ stT249 175 := by
  have hc : ((-620573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-469109127317/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-620573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c176 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((340597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2053511/10000000) (δ := 12473/1000000000) (ψ := 5473/25000) 249 205
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t176 : ((32089460127/625000000000 : ℚ) : ℝ) ≤ stT249 176 := by
  have hc : ((85143/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32089460127/625000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((85143/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c177 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((415643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473449/10000000) (δ := 1263/100000000) (ψ := 5473/25000) 249 205
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t177 : ((78099401807/1250000000000 : ℚ) : ℝ) ≤ stT249 177 := by
  have hc : ((207809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78099401807/1250000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((207809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c178 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-204519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498049/1000000) (δ := 12473/1000000000) (ψ := 5473/25000) 249 205
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t178 : ((-149719017/4882812500 : ℚ) : ℝ) ≤ stT249 178 := by
  have hc : ((-6392/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149719017/4882812500 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-6392/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c179 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-969997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3620021/5000000) (δ := 12623/1000000000) (ψ := 5473/25000) 249 206
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t179 : ((-181262012373/2500000000000 : ℚ) : ℝ) ≤ stT249 179 := by
  have hc : ((-970047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181262012373/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-970047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c180 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((61919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1886047/5000000) (δ := 39/3125000) (ψ := 5473/25000) 249 206
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t180 : ((9222873699/2000000000000 : ℚ) : ℝ) ≤ stT249 180 := by
  have hc : ((61869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9222873699/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((61869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c181 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((991649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8083/250000) (δ := 12623/1000000000) (ψ := 5473/25000) 249 206
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t181 : ((368524793553/5000000000000 : ℚ) : ℝ) ≤ stT249 181 := by
  have hc : ((991599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368524793553/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((991599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c182 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((80593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1553203/5000000) (δ := 12623/1000000000) (ψ := 5473/25000) 249 206
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t182 : ((119460430089/5000000000000 : ℚ) : ℝ) ≤ stT249 182 := by
  have hc : ((161161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119460430089/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((161161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c183 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-172091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303479/2000000) (δ := 12523/1000000000) (ψ := 5473/25000) 249 206
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t183 : ((-63610422711/1000000000000 : ℚ) : ℝ) ≤ stT249 183 := by
  have hc : ((-172101/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63610422711/1000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-172101/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c184 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-340263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362387/625000) (δ := 1561/125000000) (ψ := 5473/25000) 249 207
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t184 : ((-391974557/7812500000 : ℚ) : ℝ) ≤ stT249 184 := by
  have hc : ((-10634/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391974557/7812500000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-10634/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c185 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((56557/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121209/500000) (δ := 2503/200000000) (ψ := 5473/25000) 249 207
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t185 : ((2598613883/62500000000 : ℚ) : ℝ) ≤ stT249 185 := by
  have hc : ((7069/12500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2598613883/62500000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((7069/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c186 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((93137/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 931593/10000000) (δ := 2503/200000000) (ψ := 5473/25000) 249 207
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t186 : ((3414382101/50000000000 : ℚ) : ℝ) ≤ stT249 186 := by
  have hc : ((23283/25000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3414382101/50000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((23283/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c187 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-136551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2134719/5000000) (δ := 2503/200000000) (ψ := 5473/25000) 249 207
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t187 : ((-99892623073/10000000000000 : ℚ) : ℝ) ≤ stT249 187 := by
  have hc : ((-136601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99892623073/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-136601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c188 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-497203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7589417/10000000) (δ := 2523/200000000) (ψ := 5473/25000) 249 207
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t188 : ((-3626408111/50000000000 : ℚ) : ℝ) ≤ stT249 188 := by
  have hc : ((-124307/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3626408111/50000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-124307/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c189 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-174101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4816121/10000000) (δ := 2499/200000000) (ψ := 5473/25000) 249 208
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t189 : ((-63329016759/2500000000000 : ℚ) : ℝ) ≤ stT249 189 := by
  have hc : ((-87063/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63329016759/2500000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-87063/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c190 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((818227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1531189/10000000) (δ := 197/15625000) (ψ := 5473/25000) 249 208
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t190 : ((148391944313/2500000000000 : ℚ) : ℝ) ≤ stT249 190 := by
  have hc : ((818177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148391944313/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((818177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c191 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((384147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1736563/10000000) (δ := 2499/200000000) (ψ := 5473/25000) 249 208
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t191 : ((69485173007/1250000000000 : ℚ) : ℝ) ≤ stT249 191 := by
  have hc : ((192061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69485173007/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((192061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c192 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-102871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1246799/2500000) (δ := 2519/200000000) (ψ := 5473/25000) 249 208
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t192 : ((-18562446837/625000000000 : ℚ) : ℝ) ≤ stT249 192 := by
  have hc : ((-205767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18562446837/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-205767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c193 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-494623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1497401/2000000) (δ := 12601/1000000000) (ψ := 5473/25000) 249 209
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t193 : ((-5563367887/78125000000 : ℚ) : ℝ) ≤ stT249 193 := by
  have hc : ((-61831/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5563367887/78125000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-61831/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c194 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-17093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170797/400000) (δ := 12601/1000000000) (ψ := 5473/25000) 249 209
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t194 : ((-49106241723/5000000000000 : ℚ) : ℝ) ≤ stT249 194 := by
  have hc : ((-68397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49106241723/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-68397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c195 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((909897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1069403/10000000) (δ := 6251/500000000) (ψ := 5473/25000) 249 209
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t195 : ((325777087279/5000000000000 : ℚ) : ℝ) ≤ stT249 195 := by
  have hc : ((909847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325777087279/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((909847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c196 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((663059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2114747/10000000) (δ := 6301/500000000) (ψ := 5473/25000) 249 209
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t196 : ((94715476713/2000000000000 : ℚ) : ℝ) ≤ stT249 196 := by
  have hc : ((663009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94715476713/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((663009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c197 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-516097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5282711/10000000) (δ := 12601/1000000000) (ψ := 5473/25000) 249 209
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t197 : ((-367739769237/10000000000000 : ℚ) : ℝ) ≤ stT249 197 := by
  have hc : ((-516147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-367739769237/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-516147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c198 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-19463/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1818337/2500000) (δ := 6297/500000000) (ψ := 5473/25000) 249 210
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t198 : ((-172906011/2500000000 : ℚ) : ℝ) ≤ stT249 198 := by
  have hc : ((-2433/2500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172906011/2500000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-2433/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c199 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-84031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4137317/10000000) (δ := 12509/1000000000) (ψ := 5473/25000) 249 210
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t199 : ((-29801753721/5000000000000 : ℚ) : ℝ) ≤ stT249 199 := by
  have hc : ((-84081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29801753721/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-84081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c200 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((459193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254259/2500000) (δ := 6247/500000000) (ψ := 5473/25000) 249 210
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t200 : ((5073131997/78125000000 : ℚ) : ℝ) ≤ stT249 200 := by
  have hc : ((14349/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5073131997/78125000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((14349/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c201 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((134221/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417549/2000000) (δ := 6247/500000000) (ψ := 5473/25000) 249 210
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t201 : ((18933011559/400000000000 : ℚ) : ℝ) ≤ stT249 201 := by
  have hc : ((134211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18933011559/400000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((134211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c202 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-239719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2588513/5000000) (δ := 12509/1000000000) (ψ := 5473/25000) 249 210
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t202 : ((-658919527/19531250000 : ℚ) : ℝ) ≤ stT249 202 := by
  have hc : ((-7492/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658919527/19531250000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-7492/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c203 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-987409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3728423/5000000) (δ := 12587/1000000000) (ψ := 5473/25000) 249 211
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t203 : ((-693060936117/10000000000000 : ℚ) : ℝ) ≤ stT249 203 := by
  have hc : ((-987459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-693060936117/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-987459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c204 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-46811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4397881/10000000) (δ := 12587/1000000000) (ψ := 5473/25000) 249 211
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t204 : ((-65566104227/5000000000000 : ℚ) : ℝ) ≤ stT249 204 := by
  have hc : ((-93647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65566104227/5000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-93647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c205 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((171383/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10577/78125) (δ := 12587/1000000000) (ψ := 5473/25000) 249 211
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t205 : ((11969204439/200000000000 : ℚ) : ℝ) ≤ stT249 205 := by
  have hc : ((171373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11969204439/200000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((171373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c206 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((391867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837677/5000000) (δ := 3129/250000000) (ψ := 5473/25000) 249 211
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t206 : ((136504626093/2500000000000 : ℚ) : ℝ) ≤ stT249 206 := by
  have hc : ((195921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136504626093/2500000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((195921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c207 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-300439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 293117/625000) (δ := 12587/1000000000) (ψ := 5473/25000) 249 211
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t207 : ((-208854578961/10000000000000 : ℚ) : ℝ) ≤ stT249 207 := by
  have hc : ((-300489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208854578961/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-300489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c208 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-997847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7689887/10000000) (δ := 1577/125000000) (ψ := 5473/25000) 249 211
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t208 : ((-5405608049/78125000000 : ℚ) : ℝ) ≤ stT249 208 := by
  have hc : ((-997897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5405608049/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-997897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c209 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-427911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2516221/5000000) (δ := 3131/250000000) (ψ := 5473/25000) 249 212
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t209 : ((-59205408623/2000000000000 : ℚ) : ℝ) ≤ stT249 209 := by
  have hc : ((-427961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59205408623/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-427961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c210 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((678979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2061063/10000000) (δ := 12479/1000000000) (ψ := 5473/25000) 249 212
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t210 : ((93701028077/2000000000000 : ℚ) : ℝ) ≤ stT249 210 := by
  have hc : ((678929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93701028077/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((678929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c211 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((936433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448093/5000000) (δ := 789/62500000) (ψ := 5473/25000) 249 212
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t211 : ((161158068981/2500000000000 : ℚ) : ℝ) ≤ stT249 211 := by
  have hc : ((936383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161158068981/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((936383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c212 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((17509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959857/2500000) (δ := 3131/250000000) (ψ := 5473/25000) 249 212
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t212 : ((1501005771/625000000000 : ℚ) : ℝ) ≤ stT249 212 := by
  have hc : ((4371/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1501005771/625000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((4371/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c213 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-907269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6768851/10000000) (δ := 789/62500000) (ψ := 5473/25000) 249 212
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t213 : ((-621684998291/10000000000000 : ℚ) : ℝ) ≤ stT249 213 := by
  have hc : ((-907319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621684998291/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-907319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c214 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-2324/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1204677/2000000) (δ := 1559/125000000) (ψ := 5473/25000) 249 213
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t214 : ((-25420170789/500000000000 : ℚ) : ℝ) ≤ stT249 214 := by
  have hc : ((-74373/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25420170789/500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-74373/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c215 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((31673/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312129/1000000) (δ := 1559/125000000) (ψ := 5473/25000) 249 213
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t215 : ((2699673249/125000000000 : ℚ) : ℝ) ≤ stT249 215 := by
  have hc : ((7917/25000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2699673249/125000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((7917/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c216 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((995673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232641/10000000) (δ := 1559/125000000) (ψ := 5473/25000) 249 213
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t216 : ((677434832299/10000000000000 : ℚ) : ℝ) ≤ stT249 216 := by
  have hc : ((995623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677434832299/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((995623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c217 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((122861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41291/156250) (δ := 3143/250000000) (ψ := 5473/25000) 249 213
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t217 : ((41697483567/1250000000000 : ℚ) : ℝ) ≤ stT249 217 := by
  have hc : ((245697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41697483567/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((245697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c218 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-295009/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5504693/10000000) (δ := 12631/1000000000) (ψ := 5473/25000) 249 213
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t218 : ((-49955599431/1250000000000 : ℚ) : ℝ) ≤ stT249 218 := by
  have hc : ((-147517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49955599431/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-147517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c219 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-98009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294171/400000) (δ := 2493/200000000) (ψ := 5473/25000) 249 214
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t219 : ((-16557946083/250000000000 : ℚ) : ℝ) ≤ stT249 219 := by
  have hc : ((-49007/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16557946083/250000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-49007/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c220 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-2929/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4518289/10000000) (δ := 6319/500000000) (ψ := 5473/25000) 249 214
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t220 : ((-79006127/5000000000 : ℚ) : ℝ) ≤ stT249 220 := by
  have hc : ((-23437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79006127/5000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-23437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c221 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((778797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1695127/10000000) (δ := 6319/500000000) (ψ := 5473/25000) 249 214
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t221 : ((16370040687/312500000000 : ℚ) : ℝ) ≤ stT249 221 := by
  have hc : ((778747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16370040687/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((778747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c222 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((902143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1115211/10000000) (δ := 2493/200000000) (ψ := 5473/25000) 249 214
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t222 : ((151361282377/2500000000000 : ℚ) : ℝ) ≤ stT249 222 := by
  have hc : ((902093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151361282377/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((902093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c223 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((2803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156519/400000) (δ := 2493/200000000) (ψ := 5473/25000) 249 214
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t223 : ((930142461/2500000000000 : ℚ) : ℝ) ≤ stT249 223 := by
  have hc : ((1389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((930142461/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((1389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c224 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-223757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6698227/10000000) (δ := 6269/500000000) (ψ := 5473/25000) 249 214
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t224 : ((-149512486503/2500000000000 : ℚ) : ℝ) ≤ stT249 224 := by
  have hc : ((-447539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149512486503/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-447539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c225 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-79799/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779609/1250000) (δ := 2529/200000000) (ψ := 5473/25000) 249 215
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t225 : ((-13300673317/250000000000 : ℚ) : ℝ) ≤ stT249 225 := by
  have hc : ((-19951/25000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13300673317/250000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-19951/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c226 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((44819/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -695273/2000000) (δ := 4989/200000000) (ψ := 5473/25000) 249 215
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t226 : ((5960967147/500000000000 : ℚ) : ℝ) ≤ stT249 226 := by
  have hc : ((89613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5960967147/500000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((89613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c227 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((957901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181999/2500000) (δ := 2529/200000000) (ψ := 5473/25000) 249 215
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t227 : ((635747739273/10000000000000 : ℚ) : ℝ) ≤ stT249 227 := by
  have hc : ((957851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635747739273/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((957851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c228 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((694331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 401653/2000000) (δ := 2529/200000000) (ψ := 5473/25000) 249 215
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t228 : ((229899350373/5000000000000 : ℚ) : ℝ) ≤ stT249 228 := by
  have hc : ((694281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229899350373/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((694281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c229 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-158343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2366287/5000000) (δ := 2529/200000000) (ψ := 5473/25000) 249 215
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t229 : ((-3270393231/156250000000 : ℚ) : ℝ) ≤ stT249 229 := by
  have hc : ((-4949/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3270393231/156250000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-4949/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c230 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-123331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7444993/10000000) (δ := 2509/200000000) (ψ := 5473/25000) 249 215
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t230 : ((-325304956969/5000000000000 : ℚ) : ℝ) ≤ stT249 230 := by
  have hc : ((-493349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325304956969/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-493349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c231 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-608469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5562317/10000000) (δ := 12651/1000000000) (ψ := 5473/25000) 249 216
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t231 : ((-12511759159/312500000000 : ℚ) : ℝ) ≤ stT249 231 := by
  have hc : ((-608519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12511759159/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-608519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c232 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((102271/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1436683/5000000) (δ := 12651/1000000000) (ψ := 5473/25000) 249 216
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t232 : ((33567988761/1250000000000 : ℚ) : ℝ) ≤ stT249 232 := by
  have hc : ((204517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33567988761/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((204517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c233 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((99693/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195931/10000000) (δ := 12551/1000000000) (ψ := 5473/25000) 249 216
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t233 : ((8163462781/125000000000 : ℚ) : ℝ) ≤ stT249 233 := by
  have hc : ((12461/12500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8163462781/125000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((12461/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c234 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((68793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49401/200000) (δ := 3113/250000000) (ψ := 5473/25000) 249 216
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t234 : ((4496727421/125000000000 : ℚ) : ℝ) ≤ stT249 234 := by
  have hc : ((275147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4496727421/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((275147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c235 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-92189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5124639/10000000) (δ := 3113/250000000) (ψ := 5473/25000) 249 216
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t235 : ((-60144081471/2000000000000 : ℚ) : ℝ) ≤ stT249 235 := by
  have hc : ((-92199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60144081471/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-92199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c236 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-62463/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7767961/10000000) (δ := 1569/125000000) (ψ := 5473/25000) 249 216
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t236 : ((-65059218781/1000000000000 : ℚ) : ℝ) ≤ stT249 236 := by
  have hc : ((-499729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65059218781/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-499729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c237 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-65587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2653943/5000000) (δ := 49/3906250) (ψ := 5473/25000) 249 217
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t237 : ((-17042962961/500000000000 : ℚ) : ℝ) ≤ stT249 237 := by
  have hc : ((-262373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17042962961/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-262373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c238 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((475961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53737/200000) (δ := 3161/250000000) (ψ := 5473/25000) 249 217
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t238 : ((308486937933/10000000000000 : ℚ) : ℝ) ≤ stT249 238 := by
  have hc : ((475911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308486937933/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((475911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c239 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((999529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76769/10000000) (δ := 12559/1000000000) (ψ := 5473/25000) 249 217
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t239 : ((323254496617/5000000000000 : ℚ) : ℝ) ≤ stT249 239 := by
  have hc : ((999479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323254496617/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((999479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c240 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((106547/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2522417/10000000) (δ := 49/3906250) (ψ := 5473/25000) 249 217
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t240 : ((68769313889/2000000000000 : ℚ) : ℝ) ≤ stT249 240 := by
  have hc : ((106537/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68769313889/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((106537/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c241 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-91203/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1277693/2500000) (δ := 49/3906250) (ψ := 5473/25000) 249 217
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t241 : ((-58755492441/2000000000000 : ℚ) : ℝ) ≤ stT249 241 := by
  have hc : ((-91213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58755492441/2000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-91213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c242 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-62363/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 384421/500000) (δ := 49/3906250) (ψ := 5473/25000) 249 217
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t242 : ((-12828961377/200000000000 : ℚ) : ℝ) ≤ stT249 242 := by
  have hc : ((-498929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12828961377/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-498929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c243 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-71631/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -272627/500000) (δ := 1567/125000000) (ψ := 5473/25000) 249 218
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t243 : ((-183821470049/5000000000000 : ℚ) : ℝ) ≤ stT249 243 := by
  have hc : ((-286549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183821470049/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-286549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c244 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((80157/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2896057/10000000) (δ := 1567/125000000) (ψ := 5473/25000) 249 218
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t244 : ((6413603381/250000000000 : ℚ) : ℝ) ≤ stT249 244 := by
  have hc : ((80147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6413603381/250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((80147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c245 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((247553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -350063/10000000) (δ := 3117/125000000) (ψ := 5473/25000) 249 218
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t245 : ((79073842239/1250000000000 : ℚ) : ℝ) ≤ stT249 245 := by
  have hc : ((495081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79073842239/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((495081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c246 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((641581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2185597/10000000) (δ := 3159/250000000) (ψ := 5473/25000) 249 218
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t246 : ((51128096107/1250000000000 : ℚ) : ℝ) ≤ stT249 246 := by
  have hc : ((641531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51128096107/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((641531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c247 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-308471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942191/2000000) (δ := 3159/250000000) (ψ := 5473/25000) 249 218
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t247 : ((-39261456897/2000000000000 : ℚ) : ℝ) ≤ stT249 247 := by
  have hc : ((-308521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39261456897/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-308521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c248 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-968627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 903263/1250000) (δ := 3159/250000000) (ψ := 5473/25000) 249 218
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t248 : ((-615110863677/10000000000000 : ℚ) : ℝ) ≤ stT249 248 := by
  have hc : ((-968677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615110863677/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-968677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c249 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-731109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5976857/10000000) (δ := 12629/1000000000) (ψ := 5473/25000) 249 219
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t249 : ((-18534149491/400000000000 : ℚ) : ℝ) ≤ stT249 249 := by
  have hc : ((-731159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18534149491/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-731159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c250 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((177131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1740907/5000000) (δ := 6287/500000000) (ψ := 5473/25000) 249 219
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t250 : ((22399152771/2000000000000 : ℚ) : ℝ) ≤ stT249 250 := by
  have hc : ((177081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22399152771/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((177081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c251 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((23039/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -498397/5000000) (δ := 6287/500000000) (ψ := 5473/25000) 249 219
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t251 : ((29082579147/500000000000 : ℚ) : ℝ) ≤ stT249 251 := by
  have hc : ((92151/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29082579147/500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((92151/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c252 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((830199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184791/1250000) (δ := 6237/500000000) (ψ := 5473/25000) 249 219
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t252 : ((26147203053/500000000000 : ℚ) : ℝ) ≤ stT249 252 := by
  have hc : ((830149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26147203053/500000000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((830149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c253 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-3337/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3943677/10000000) (δ := 6237/500000000) (ψ := 5473/25000) 249 219
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t253 : ((-211367259/500000000000 : ℚ) : ℝ) ≤ stT249 253 := by
  have hc : ((-1681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211367259/500000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-1681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c254 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-417719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279863/2000000) (δ := 6237/500000000) (ψ := 5473/25000) 249 219
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t254 : ((-63993159/1220703125 : ℚ) : ℝ) ≤ stT249 254 := by
  have hc : ((-26109/31250 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63993159/1220703125 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-26109/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c255 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-922407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6862659/10000000) (δ := 12481/1000000000) (ψ := 5473/25000) 249 220
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t255 : ((-23106625393/400000000000 : ℚ) : ℝ) ≤ stT249 255 := by
  have hc : ((-922457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23106625393/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-922457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c256 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-198381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -276641/625000) (δ := 12581/1000000000) (ψ := 5473/25000) 249 220
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t256 : ((-124019573431/10000000000000 : ℚ) : ℝ) ≤ stT249 256 := by
  have hc : ((-198431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124019573431/10000000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-198431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c257 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((139377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -999689/5000000) (δ := 6261/500000000) (ψ := 5473/25000) 249 220
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t257 : ((43467312997/1000000000000 : ℚ) : ℝ) ≤ stT249 257 := by
  have hc : ((139367/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43467312997/1000000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((139367/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c258 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((15407/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418101/10000000) (δ := 12481/1000000000) (ψ := 5473/25000) 249 220
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t258 : ((76731843357/1250000000000 : ℚ) : ℝ) ≤ stT249 258 := by
  have hc : ((492999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76731843357/1250000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((492999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c259 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((42621/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1413121/5000000) (δ := 6261/500000000) (ψ := 5473/25000) 249 220
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t259 : ((3310032663/125000000000 : ℚ) : ℝ) ≤ stT249 259 := by
  have hc : ((5327/12500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3310032663/125000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((5327/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c260 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-248113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1306277/2500000) (δ := 6261/500000000) (ψ := 5473/25000) 249 220
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t260 : ((-38472184003/1250000000000 : ℚ) : ℝ) ≤ stT249 260 := by
  have hc : ((-124069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38472184003/1250000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-124069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c261 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-39817/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7614761/10000000) (δ := 6261/500000000) (ψ := 5473/25000) 249 220
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t261 : ((-4929472743/80000000000 : ℚ) : ℝ) ≤ stT249 261 := by
  have hc : ((-39819/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4929472743/80000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-39819/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c262 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-163769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57127/100000) (δ := 7483/200000000) (ψ := 5473/25000) 249 221
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t262 : ((-202369404089/5000000000000 : ℚ) : ℝ) ≤ stT249 262 := by
  have hc : ((-327563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202369404089/5000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-327563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c263 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((46429/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1670643/5000000) (δ := 1561/125000000) (ψ := 5473/25000) 249 221
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t263 : ((14311581147/1000000000000 : ℚ) : ℝ) ≤ stT249 263 := by
  have hc : ((46419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14311581147/1000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((46419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c264 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((36973/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244709/2500000) (δ := 2343/62500000) (ψ := 5473/25000) 249 221
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t264 : ((22754060747/400000000000 : ℚ) : ℝ) ≤ stT249 264 := by
  have hc : ((36971/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22754060747/400000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((36971/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c265 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((426299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374649/10000000) (δ := 2523/200000000) (ψ := 5473/25000) 249 221
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t265 : ((26185798683/500000000000 : ℚ) : ℝ) ≤ stT249 265 := by
  have hc : ((213137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26185798683/500000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((213137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c266 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((41491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29057/78125) (δ := 3147/250000000) (ψ := 5473/25000) 249 221
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t266 : ((12712210887/2500000000000 : ℚ) : ℝ) ≤ stT249 266 := by
  have hc : ((20733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12712210887/2500000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((20733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c267 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-752101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3027551/5000000) (δ := 2523/200000000) (ψ := 5473/25000) 249 221
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t267 : ((-460309642641/10000000000000 : ℚ) : ℝ) ≤ stT249 267 := by
  have hc : ((-752151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-460309642641/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-752151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c268 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-488881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7325769/10000000) (δ := 2499/200000000) (ψ := 5473/25000) 249 222
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t268 : ((-4666363317/78125000000 : ℚ) : ℝ) ≤ stT249 268 := by
  have hc : ((-244453/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4666363317/78125000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-244453/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c269 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-418811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -500733/1000000) (δ := 2499/200000000) (ψ := 5473/25000) 249 222
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t269 : ((-255384159171/10000000000000 : ℚ) : ℝ) ≤ stT249 269 := by
  have hc : ((-418861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255384159171/10000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-418861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c270 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((59027/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1348741/5000000) (δ := 197/15625000) (ψ := 5473/25000) 249 222
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t270 : ((7183769607/250000000000 : ℚ) : ℝ) ≤ stT249 270 := by
  have hc : ((236083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7183769607/250000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((236083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c271 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((987471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -396161/10000000) (δ := 2519/200000000) (ψ := 5473/25000) 249 222
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t271 : ((18744212843/312500000000 : ℚ) : ℝ) ≤ stT249 271 := by
  have hc : ((987421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18744212843/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((987421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c272 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((181441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1896631/10000000) (δ := 2519/200000000) (ψ := 5473/25000) 249 222
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t272 : ((220014350523/5000000000000 : ℚ) : ℝ) ≤ stT249 272 := by
  have hc : ((362857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220014350523/5000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((362857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c273 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-101437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4181019/10000000) (δ := 2499/200000000) (ψ := 5473/25000) 249 222
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t273 : ((-15355693509/2500000000000 : ℚ) : ℝ) ≤ stT249 273 := by
  have hc : ((-101487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15355693509/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-101487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c274 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-847923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 807141/1250000) (δ := 2499/200000000) (ψ := 5473/25000) 249 222
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t274 : ((-512279992679/10000000000000 : ℚ) : ℝ) ≤ stT249 274 := by
  have hc : ((-847973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512279992679/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-847973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c275 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-46997/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -698313/1000000) (δ := 12503/1000000000) (ψ := 5473/25000) 249 223
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t275 : ((-56683558977/1000000000000 : ℚ) : ℝ) ≤ stT249 275 := by
  have hc : ((-93999/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56683558977/1000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-93999/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c276 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-313271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236179/500000) (δ := 63/5000000) (ψ := 5473/25000) 249 223
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t276 : ((-18859730953/1000000000000 : ℚ) : ℝ) ≤ stT249 276 := by
  have hc : ((-313321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18859730953/1000000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-313321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c277 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((549631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -309023/1250000) (δ := 1/80000) (ψ := 5473/25000) 249 223
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t277 : ((330210797621/10000000000000 : ℚ) : ℝ) ≤ stT249 277 := by
  have hc : ((549581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330210797621/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((549581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c278 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((99581/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -228943/10000000) (δ := 1/80000) (ψ := 5473/25000) 249 223
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t278 : ((93315159/1562500000 : ℚ) : ℝ) ≤ stT249 278 := by
  have hc : ((12447/12500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93315159/1562500000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((12447/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c279 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((173731/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1003103/5000000) (δ := 12603/1000000000) (ψ := 5473/25000) 249 223
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t279 : ((52001243227/1250000000000 : ℚ) : ℝ) ≤ stT249 279 := by
  have hc : ((347437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52001243227/1250000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((347437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c280 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-30569/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 529181/1250000) (δ := 63/5000000) (ψ := 5473/25000) 249 223
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t280 : ((-7310385249/1000000000000 : ℚ) : ℝ) ≤ stT249 280 := by
  have hc : ((-61163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7310385249/1000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-61163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c281 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-423487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6452661/10000000) (δ := 12503/1000000000) (ψ := 5473/25000) 249 223
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t281 : ((-631615209/12500000000 : ℚ) : ℝ) ≤ stT249 281 := by
  have hc : ((-52939/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-631615209/12500000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-52939/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c282 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-947963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7043933/10000000) (δ := 1261/100000000) (ψ := 5473/25000) 249 224
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t282 : ((-141133539349/2500000000000 : ℚ) : ℝ) ≤ stT249 282 := by
  have hc : ((-948013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141133539349/2500000000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-948013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c283 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-89323/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -605051/1250000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 224
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t283 : ((-106209010569/5000000000000 : ℚ) : ℝ) ≤ stT249 283 := by
  have hc : ((-178671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106209010569/5000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-178671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c284 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((98151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2644601/10000000) (δ := 1261/100000000) (ψ := 5473/25000) 249 224
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t284 : ((5823588799/200000000000 : ℚ) : ℝ) ≤ stT249 284 := by
  have hc : ((98141/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5823588799/200000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((98141/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c285 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((983369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3567/78125) (δ := 1251/100000000) (ψ := 5473/25000) 249 224
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t285 : ((145616760753/2500000000000 : ℚ) : ℝ) ≤ stT249 285 := by
  have hc : ((983319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145616760753/2500000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((983319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c286 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((771537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344771/2000000) (δ := 1261/100000000) (ψ := 5473/25000) 249 224
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t286 : ((28511845059/625000000000 : ℚ) : ℝ) ≤ stT249 286 := by
  have hc : ((771487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28511845059/625000000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((771487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c287 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((759/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3896629/10000000) (δ := 1261/100000000) (ψ := 5473/25000) 249 224
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t287 : ((3569429207/5000000000000 : ℚ) : ℝ) ≤ stT249 287 := by
  have hc : ((6047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3569429207/5000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((6047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c288 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-376933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378863/625000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 224
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t288 : ((-13882797703/312500000000 : ℚ) : ℝ) ≤ stT249 288 := by
  have hc : ((-188479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13882797703/312500000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-188479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c289 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-98933/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3744223/5000000) (δ := 6293/500000000) (ψ := 5473/25000) 249 225
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t289 : ((-7274861671/125000000000 : ℚ) : ℝ) ≤ stT249 289 := by
  have hc : ((-49469/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7274861671/125000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-49469/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c290 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-534961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166817/312500) (δ := 6243/500000000) (ψ := 5473/25000) 249 225
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t290 : ((-314169694431/10000000000000 : ℚ) : ℝ) ≤ stT249 290 := by
  have hc : ((-535011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314169694431/10000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-535011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c291 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((288511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199707/625000) (δ := 12517/1000000000) (ψ := 5473/25000) 249 225
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t291 : ((16909872281/1000000000000 : ℚ) : ℝ) ≤ stT249 291 := by
  have hc : ((288461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16909872281/1000000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((288461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c292 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((911489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264941/2500000) (δ := 6293/500000000) (ψ := 5473/25000) 249 225
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t292 : ((106675731999/2000000000000 : ℚ) : ℝ) ≤ stT249 292 := by
  have hc : ((911439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106675731999/2000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((911439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c293 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((910057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068439/10000000) (δ := 6293/500000000) (ψ := 5473/25000) 249 225
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t293 : ((265815774721/5000000000000 : ℚ) : ℝ) ≤ stT249 293 := by
  have hc : ((910007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265815774721/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((910007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c294 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((29079/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3189359/10000000) (δ := 6243/500000000) (ψ := 5473/25000) 249 225
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t294 : ((8478138307/500000000000 : ℚ) : ℝ) ≤ stT249 294 := by
  have hc : ((14537/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8478138307/500000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((14537/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c295 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-8173/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66289/125000) (δ := 6243/500000000) (ψ := 5473/25000) 249 225
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t295 : ((-152286830103/5000000000000 : ℚ) : ℝ) ≤ stT249 295 := by
  have hc : ((-261561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152286830103/5000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-261561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c296 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-246063/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3704861/5000000) (δ := 6293/500000000) (ψ := 5473/25000) 249 225
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t296 : ((-286057355089/5000000000000 : ℚ) : ℝ) ≤ stT249 296 := by
  have hc : ((-492151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286057355089/5000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-492151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c297 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-24647/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1239747/2000000) (δ := 3131/250000000) (ψ := 5473/25000) 249 226
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t297 : ((-228840803643/5000000000000 : ℚ) : ℝ) ≤ stT249 297 := by
  have hc : ((-394377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228840803643/5000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-394377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c298 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-71673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2053163/5000000) (δ := 12479/1000000000) (ψ := 5473/25000) 249 226
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t298 : ((-8309611611/2000000000000 : ℚ) : ℝ) ≤ stT249 298 := by
  have hc : ((-71723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).2
  have h0 : (0:ℝ) ≤ ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8309611611/2000000000000 : ℚ) : ℝ)
      = ((115857/2000000 : ℚ) : ℝ) * ((-71723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c299 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((690689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2020889/10000000) (δ := 12579/1000000000) (ψ := 5473/25000) 249 226
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t299 : ((199703101323/5000000000000 : ℚ) : ℝ) ≤ stT249 299 := by
  have hc : ((690639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199703101323/5000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((690639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c300 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((199947/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57577/10000000) (δ := 789/62500000) (ψ := 5473/25000) 249 226
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t300 : ((2308672539/40000000000 : ℚ) : ℝ) ≤ stT249 300 := by
  have hc : ((199937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2308672539/40000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((199937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c301 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((658741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 532283/2500000) (δ := 12479/1000000000) (ψ := 5473/25000) 249 226
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t301 : ((37966290549/1000000000000 : ℚ) : ℝ) ≤ stT249 301 := by
  have hc : ((658691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37966290549/1000000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((658691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c302 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-106537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52423/125000) (δ := 12479/1000000000) (ψ := 5473/25000) 249 226
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t302 : ((-15333499233/2500000000000 : ℚ) : ℝ) ≤ stT249 302 := by
  have hc : ((-106587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15333499233/2500000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-106587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c303 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-801551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6251701/10000000) (δ := 789/62500000) (ψ := 5473/25000) 249 226
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t303 : ((-92101550097/2000000000000 : ℚ) : ℝ) ≤ stT249 303 := by
  have hc : ((-801601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92101550097/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-801601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c304 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-98393/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7405187/10000000) (δ := 12631/1000000000) (ψ := 5473/25000) 249 227
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t304 : ((-1410879723/25000000000 : ℚ) : ℝ) ≤ stT249 304 := by
  have hc : ((-49199/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1410879723/25000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-49199/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c305 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-135657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5360897/10000000) (δ := 12631/1000000000) (ψ := 5473/25000) 249 227
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t305 : ((-155368440061/5000000000000 : ℚ) : ℝ) ≤ stT249 305 := by
  have hc : ((-271339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155368440061/5000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-271339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c306 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((239173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1661603/5000000) (δ := 1559/125000000) (ψ := 5473/25000) 249 227
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t306 : ((136697293303/10000000000000 : ℚ) : ℝ) ≤ stT249 306 := by
  have hc : ((239123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136697293303/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((239123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c307 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((434679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1292237/10000000) (δ := 12631/1000000000) (ψ := 5473/25000) 249 227
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t307 : ((12403503871/250000000000 : ℚ) : ℝ) ≤ stT249 307 := by
  have hc : ((217327/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12403503871/250000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((217327/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c308 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((59839/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 732133/10000000) (δ := 12631/1000000000) (ψ := 5473/25000) 249 227
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t308 : ((136378404987/2500000000000 : ℚ) : ℝ) ≤ stT249 308 := by
  have hc : ((478687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136378404987/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((478687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c309 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((56701/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1374983/5000000) (δ := 3143/250000000) (ψ := 5473/25000) 249 227
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t309 : ((1612625469/62500000000 : ℚ) : ℝ) ≤ stT249 309 := by
  have hc : ((226779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1612625469/62500000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((226779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c310 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-6551/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297579/625000) (δ := 12531/1000000000) (ψ := 5473/25000) 249 227
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t310 : ((-232580439/12500000000 : ℚ) : ℝ) ≤ stT249 310 := by
  have hc : ((-819/2500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232580439/12500000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-819/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c311 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-453407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135323/200000) (δ := 12631/1000000000) (ψ := 5473/25000) 249 227
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t311 : ((-4017464199/78125000000 : ℚ) : ℝ) ≤ stT249 311 := by
  have hc : ((-56679/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4017464199/78125000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-56679/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c312 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-934407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867933/1250000) (δ := 6269/500000000) (ψ := 5473/25000) 249 228
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t312 : ((-529032551523/10000000000000 : ℚ) : ℝ) ≤ stT249 312 := by
  have hc : ((-934457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529032551523/10000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-934457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c313 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-24901/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618933/1250000) (δ := 6269/500000000) (ψ := 5473/25000) 249 228
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t313 : ((-56306632761/2500000000000 : ℚ) : ℝ) ≤ stT249 313 := by
  have hc : ((-199233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56306632761/2500000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-199233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c314 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((375069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1482907/5000000) (δ := 2513/200000000) (ψ := 5473/25000) 249 228
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t314 : ((52908805577/2500000000000 : ℚ) : ℝ) ≤ stT249 314 := by
  have hc : ((375019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52908805577/2500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((375019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c315 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((461579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19729/200000) (δ := 6319/500000000) (ψ := 5473/25000) 249 228
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t315 : ((32507017443/625000000000 : ℚ) : ℝ) ≤ stT249 315 := by
  have hc : ((230777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32507017443/625000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((230777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c316 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((923131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493313/5000000) (δ := 6319/500000000) (ψ := 5473/25000) 249 228
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t316 : ((519272754983/10000000000000 : ℚ) : ℝ) ≤ stT249 316 := by
  have hc : ((923081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519272754983/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((923081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c317 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((189831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1476707/5000000) (δ := 2513/200000000) (ψ := 5473/25000) 249 228
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t317 : ((10660548893/500000000000 : ℚ) : ℝ) ≤ stT249 317 := by
  have hc : ((94903/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10660548893/500000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((94903/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c318 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-192321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122851/250000) (δ := 2513/200000000) (ψ := 5473/25000) 249 228
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t318 : ((-53931221729/2500000000000 : ℚ) : ℝ) ≤ stT249 318 := by
  have hc : ((-96173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53931221729/2500000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-96173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c319 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-923317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3434283/5000000) (δ := 6269/500000000) (ψ := 5473/25000) 249 228
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t319 : ((-516986719731/10000000000000 : ℚ) : ℝ) ≤ stT249 319 := by
  have hc : ((-923367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-516986719731/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-923367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c320 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-926741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6891097/10000000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 229
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t320 : ((-518091924447/10000000000000 : ℚ) : ℝ) ≤ stT249 320 := by
  have hc : ((-926791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518091924447/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-926791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c321 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-99357/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1237193/2500000) (δ := 6323/500000000) (ψ := 5473/25000) 249 229
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t321 : ((-55462688947/2500000000000 : ℚ) : ℝ) ≤ stT249 321 := by
  have hc : ((-198739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55462688947/2500000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-198739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c322 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((14307/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753137/2500000) (δ := 6323/500000000) (ψ := 5473/25000) 249 229
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t322 : ((797186179/40000000000 : ℚ) : ℝ) ≤ stT249 322 := by
  have hc : ((2861/8000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((797186179/40000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((2861/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c323 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((181549/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10823/100000) (δ := 6323/500000000) (ψ := 5473/25000) 249 229
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t323 : ((50505420573/1000000000000 : ℚ) : ℝ) ≤ stT249 323 := by
  have hc : ((181539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50505420573/1000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((181539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c324 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((943821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210493/2500000) (δ := 6323/500000000) (ψ := 5473/25000) 249 229
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t324 : ((104863339581/2000000000000 : ℚ) : ℝ) ≤ stT249 324 := by
  have hc : ((943771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104863339581/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((943771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c325 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((112483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 690067/2500000) (δ := 6323/500000000) (ψ := 5473/25000) 249 229
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t325 : ((1247747727/50000000000 : ℚ) : ℝ) ≤ stT249 325 := by
  have hc : ((224941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1247747727/50000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((224941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c326 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-58777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 584089/1250000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 229
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t326 : ((-32559121163/2000000000000 : ℚ) : ℝ) ≤ stT249 326 := by
  have hc : ((-58787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32559121163/2000000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-58787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c327 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-109101/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1315861/2000000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 229
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t327 : ((-120673054929/2500000000000 : ℚ) : ℝ) ≤ stT249 327 := by
  have hc : ((-436429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120673054929/2500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-436429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c328 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-968801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445571/2000000) (δ := 253/20000000) (ψ := 5473/25000) 249 230
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t328 : ((-267479415229/5000000000000 : ℚ) : ℝ) ≤ stT249 328 := by
  have hc : ((-968851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267479415229/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-968851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c329 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-133297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2666451/5000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 230
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t329 : ((-73495926921/2500000000000 : ℚ) : ℝ) ≤ stT249 329 := by
  have hc : ((-266619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73495926921/2500000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-266619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c330 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((48031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3443677/10000000) (δ := 12453/1000000000) (ψ := 5473/25000) 249 230
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t330 : ((52866543797/5000000000000 : ℚ) : ℝ) ≤ stT249 330 := by
  have hc : ((96037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52866543797/5000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((96037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c331 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((405753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1560179/10000000) (δ := 251/20000000) (ψ := 5473/25000) 249 230
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t331 : ((6968999671/156250000000 : ℚ) : ℝ) ≤ stT249 331 := by
  have hc : ((12679/15625 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6968999671/156250000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((12679/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c332 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((495969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63531/2000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 230
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t332 : ((34023060253/625000000000 : ℚ) : ℝ) ≤ stT249 332 := by
  have hc : ((61993/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34023060253/625000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((61993/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c333 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((640283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2189823/10000000) (δ := 253/20000000) (ψ := 5473/25000) 249 230
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t333 : ((87711280767/2500000000000 : ℚ) : ℝ) ≤ stT249 333 := by
  have hc : ((640233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87711280767/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((640233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c334 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-51737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 405639/1000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 230
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t334 : ((-3542075439/1250000000000 : ℚ) : ℝ) ≤ stT249 334 := by
  have hc : ((-51787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3542075439/1250000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-51787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c335 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-714683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739677/1250000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 230
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t335 : ((-390500807147/10000000000000 : ℚ) : ℝ) ≤ stT249 335 := by
  have hc : ((-714733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-390500807147/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-714733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c336 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-999473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7772839/10000000) (δ := 251/20000000) (ψ := 5473/25000) 249 230
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t336 : ((-109056955007/2000000000000 : ℚ) : ℝ) ≤ stT249 336 := by
  have hc : ((-999523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109056955007/2000000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-999523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c337 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-30399/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6085179/10000000) (δ := 12643/1000000000) (ψ := 5473/25000) 249 231
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t337 : ((-3312097747/80000000000 : ℚ) : ℝ) ≤ stT249 337 := by
  have hc : ((-30401/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3312097747/80000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-30401/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c338 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-1956/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4240773/10000000) (δ := 157/12500000) (ψ := 5473/25000) 249 231
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t338 : ((-34059202193/5000000000000 : ℚ) : ℝ) ≤ stT249 338 := by
  have hc : ((-62617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34059202193/5000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-62617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c339 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((143239/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1200861/5000000) (δ := 12643/1000000000) (ψ := 5473/25000) 249 231
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t339 : ((248927657/8000000000 : ℚ) : ℝ) ≤ stT249 339 := by
  have hc : ((286453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).1
  have hw2 : ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((869/16000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((248927657/8000000000 : ℚ) : ℝ)
      = ((869/16000 : ℚ) : ℝ) * ((286453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c340 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((60893/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142037/2500000) (δ := 12543/1000000000) (ψ := 5473/25000) 249 231
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t340 : ((132088649397/2500000000000 : ℚ) : ℝ) ≤ stT249 340 := by
  have hc : ((487119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132088649397/2500000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((487119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c341 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((109457/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126001/1000000) (δ := 12543/1000000000) (ψ := 5473/25000) 249 231
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t341 : ((23708345859/500000000000 : ℚ) : ℝ) ≤ stT249 341 := by
  have hc : ((437803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23708345859/500000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((437803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c342 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((165633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3082877/10000000) (δ := 623/50000000) (ψ := 5473/25000) 249 231
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t342 : ((5596908669/312500000000 : ℚ) : ℝ) ≤ stT249 342 := by
  have hc : ((20701/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5596908669/312500000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((20701/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c343 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-94899/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490039/1000000) (δ := 12543/1000000000) (ψ := 5473/25000) 249 231
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t343 : ((-2049898577/100000000000 : ℚ) : ℝ) ≤ stT249 343 := by
  have hc : ((-189823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2049898577/100000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-189823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c344 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-44879/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1678153/2500000) (δ := 12543/1000000000) (ψ := 5473/25000) 249 231
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t344 : ((-12099244533/250000000000 : ℚ) : ℝ) ≤ stT249 344 := by
  have hc : ((-89763/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12099244533/250000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-89763/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c345 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-192953/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3594179/5000000) (δ := 12467/1000000000) (ψ := 5473/25000) 249 232
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t345 : ((-51943902933/1000000000000 : ℚ) : ℝ) ≤ stT249 345 := by
  have hc : ((-192963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51943902933/1000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-192963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c346 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-275627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168333/312500) (δ := 12567/1000000000) (ψ := 5473/25000) 249 232
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t346 : ((-9261976113/312500000000 : ℚ) : ℝ) ≤ stT249 346 := by
  have hc : ((-68913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9261976113/312500000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-68913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c347 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((134341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3590121/10000000) (δ := 12567/1000000000) (ψ := 5473/25000) 249 232
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t347 : ((18022792237/2500000000000 : ℚ) : ℝ) ≤ stT249 347 := by
  have hc : ((134291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18022792237/2500000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((134291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c348 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((150427/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1798753/10000000) (δ := 12467/1000000000) (ψ := 5473/25000) 249 232
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t348 : ((10078991919/250000000000 : ℚ) : ℝ) ≤ stT249 348 := by
  have hc : ((150417/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10078991919/250000000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((150417/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c349 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((249997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12489/10000000) (δ := 12567/1000000000) (ψ := 5473/25000) 249 232
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t349 : ((267626906103/5000000000000 : ℚ) : ℝ) ≤ stT249 349 := by
  have hc : ((499969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267626906103/5000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((499969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c350 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((380013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55269/312500) (δ := 12567/1000000000) (ψ := 5473/25000) 249 232
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t350 : ((25388993217/625000000000 : ℚ) : ℝ) ≤ stT249 350 := by
  have hc : ((94997/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25388993217/625000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((94997/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c351 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((9521/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1772331/5000000) (δ := 3159/250000000) (ψ := 5473/25000) 249 232
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t351 : ((31751631/3906250000 : ℚ) : ℝ) ≤ stT249 351 := by
  have hc : ((76143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31751631/3906250000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((76143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c352 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-21093/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5315613/10000000) (δ := 12567/1000000000) (ψ := 5473/25000) 249 232
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t352 : ((-1124367719/40000000000 : ℚ) : ℝ) ≤ stT249 352 := by
  have hc : ((-4219/8000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1124367719/40000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-4219/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c353 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-19053/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7081583/10000000) (δ := 12467/1000000000) (ψ := 5473/25000) 249 232
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t353 : ((-5070717169/100000000000 : ℚ) : ℝ) ≤ stT249 353 := by
  have hc : ((-9527/10000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5070717169/100000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-9527/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c354 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-230707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686539/1000000) (δ := 6237/500000000) (ψ := 5473/25000) 249 233
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t354 : ((-49050504261/1000000000000 : ℚ) : ℝ) ≤ stT249 354 := by
  have hc : ((-461439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49050504261/1000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-461439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c355 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-227771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2554721/5000000) (δ := 6237/500000000) (ψ := 5473/25000) 249 233
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t355 : ((-6045079401/250000000000 : ℚ) : ℝ) ≤ stT249 355 := by
  have hc : ((-56949/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6045079401/250000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-56949/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c356 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((451/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -67167/200000) (δ := 12629/1000000000) (ψ := 5473/25000) 249 233
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t356 : ((1194880491/100000000000 : ℚ) : ℝ) ≤ stT249 356 := by
  have hc : ((4509/20000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1194880491/100000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((4509/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c357 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((799163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1612237/10000000) (δ := 6237/500000000) (ψ := 5473/25000) 249 233
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t357 : ((52866918741/1250000000000 : ℚ) : ℝ) ≤ stT249 357 := by
  have hc : ((799113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52866918741/1250000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((799113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c358 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((998669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6451/500000) (δ := 6237/500000000) (ψ := 5473/25000) 249 233
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t358 : ((131946529851/2500000000000 : ℚ) : ℝ) ≤ stT249 358 := by
  have hc : ((998619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131946529851/2500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((998619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c359 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((146859/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1865421/10000000) (δ := 12629/1000000000) (ψ := 5473/25000) 249 233
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t359 : ((77503818371/2000000000000 : ℚ) : ℝ) ≤ stT249 359 := by
  have hc : ((146849/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77503818371/2000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((146849/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c360 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((131601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359703/1000000) (δ := 6287/500000000) (ψ := 5473/25000) 249 233
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t360 : ((34666714173/5000000000000 : ℚ) : ℝ) ≤ stT249 360 := by
  have hc : ((131551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34666714173/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((131551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c361 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-265049/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2661891/5000000) (δ := 12629/1000000000) (ψ := 5473/25000) 249 233
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t361 : ((-17439085923/625000000000 : ℚ) : ℝ) ≤ stT249 361 := by
  have hc : ((-132537/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17439085923/625000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-132537/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c362 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-948201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1761451/2500000) (δ := 12529/1000000000) (ψ := 5473/25000) 249 233
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t362 : ((-498390294839/10000000000000 : ℚ) : ℝ) ≤ stT249 362 := by
  have hc : ((-948251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498390294839/10000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-948251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c363 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-186923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6944931/10000000) (δ := 12621/1000000000) (ψ := 5473/25000) 249 234
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t363 : ((-1533037533/31250000000 : ℚ) : ℝ) ≤ stT249 363 := by
  have hc : ((-186933/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1533037533/31250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-186933/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c364 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-31173/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5232433/10000000) (δ := 6241/500000000) (ψ := 5473/25000) 249 234
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t364 : ((-130725981487/5000000000000 : ℚ) : ℝ) ≤ stT249 364 := by
  have hc : ((-249409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130725981487/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-249409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c365 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((160261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -881151/2500000) (δ := 6291/500000000) (ψ := 5473/25000) 249 234
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t365 : ((83858122253/10000000000000 : ℚ) : ℝ) ≤ stT249 365 := by
  have hc : ((160211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83858122253/10000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((160211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c366 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((373061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -455361/2500000) (δ := 6291/500000000) (ψ := 5473/25000) 249 234
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t366 : ((12186806343/312500000000 : ℚ) : ℝ) ≤ stT249 366 := by
  have hc : ((93259/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12186806343/312500000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((93259/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c367 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((998791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122953/10000000) (δ := 6241/500000000) (ψ := 5473/25000) 249 234
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t367 : ((104267561659/2000000000000 : ℚ) : ℝ) ≤ stT249 367 := by
  have hc : ((998741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104267561659/2000000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((998741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c368 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((161797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392733/2500000) (δ := 6291/500000000) (ψ := 5473/25000) 249 234
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t368 : ((42168649041/1000000000000 : ℚ) : ℝ) ≤ stT249 368 := by
  have hc : ((161787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42168649041/1000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((161787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c369 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((263561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326021/1000000) (δ := 6241/500000000) (ψ := 5473/25000) 249 234
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t369 : ((137178292869/10000000000000 : ℚ) : ℝ) ≤ stT249 369 := by
  have hc : ((263511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137178292869/10000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((263511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c370 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-396023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309059/625000) (δ := 6241/500000000) (ψ := 5473/25000) 249 234
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t370 : ((-51477211737/2500000000000 : ℚ) : ℝ) ≤ stT249 370 := by
  have hc : ((-396073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51477211737/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-396073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c371 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-220399/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6625071/10000000) (δ := 12621/1000000000) (ψ := 5473/25000) 249 234
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t371 : ((-9154571241/200000000000 : ℚ) : ℝ) ≤ stT249 371 := by
  have hc : ((-440823/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9154571241/200000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-440823/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c372 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-984077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3703623/5000000) (δ := 12589/1000000000) (ψ := 5473/25000) 249 235
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t372 : ((-127561557613/2500000000000 : ℚ) : ℝ) ≤ stT249 372 := by
  have hc : ((-984127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127561557613/2500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-984127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c373 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-132423/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5736083/10000000) (δ := 6257/500000000) (ψ := 5473/25000) 249 235
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t373 : ((-68571291173/2000000000000 : ℚ) : ℝ) ≤ stT249 373 := by
  have hc : ((-132433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68571291173/2000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-132433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c374 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-28479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -508683/1250000) (δ := 6307/500000000) (ψ := 5473/25000) 249 235
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t374 : ((-57574517/19531250000 : ℚ) : ℝ) ≤ stT249 374 := by
  have hc : ((-3563/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57574517/19531250000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-3563/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c375 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((285579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1203601/5000000) (δ := 6257/500000000) (ψ := 5473/25000) 249 235
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t375 : ((73729614469/2500000000000 : ℚ) : ℝ) ≤ stT249 375 := by
  have hc : ((142777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73729614469/2500000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((142777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c376 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((191081/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374711/5000000) (δ := 12489/1000000000) (ψ := 5473/25000) 249 235
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t376 : ((9853722541/200000000000 : ℚ) : ℝ) ≤ stT249 376 := by
  have hc : ((191071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9853722541/200000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((191071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c377 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((935341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451969/5000000) (δ := 12489/1000000000) (ψ := 5473/25000) 249 235
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t377 : ((240849591283/5000000000000 : ℚ) : ℝ) ≤ stT249 377 := by
  have hc : ((935291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240849591283/5000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((935291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c378 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((130591/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127647/500000) (δ := 6307/500000000) (ψ := 5473/25000) 249 235
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t378 : ((16790567001/625000000000 : ℚ) : ℝ) ≤ stT249 378 := by
  have hc : ((261157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16790567001/625000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((261157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c379 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-27013/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262353/625000) (δ := 12589/1000000000) (ψ := 5473/25000) 249 235
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t379 : ((-13882080483/2500000000000 : ℚ) : ℝ) ≤ stT249 379 := by
  have hc : ((-54051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13882080483/2500000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-54051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c380 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-86511/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1167587/2000000) (δ := 6257/500000000) (ψ := 5473/25000) 249 235
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t380 : ((-17752993631/500000000000 : ℚ) : ℝ) ≤ stT249 380 := by
  have hc : ((-346069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17752993631/500000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-346069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c381 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-988467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7473927/10000000) (δ := 6307/500000000) (ψ := 5473/25000) 249 235
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t381 : ((-126608268843/2500000000000 : ℚ) : ℝ) ≤ stT249 381 := by
  have hc : ((-988517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126608268843/2500000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-988517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c382 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-175451/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6602277/10000000) (δ := 12607/1000000000) (ψ := 5473/25000) 249 236
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t382 : ((-17954748669/400000000000 : ℚ) : ℝ) ≤ stT249 382 := by
  have hc : ((-175461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17954748669/400000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-175461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c383 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-101747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39799/80000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 236
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t383 : ((-103993528063/5000000000000 : ℚ) : ℝ) ≤ stT249 383 := by
  have hc : ((-203519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103993528063/5000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-203519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c384 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((228113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837911/2500000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 236
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t384 : ((11638282953/1000000000000 : ℚ) : ℝ) ≤ stT249 384 := by
  have hc : ((228063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11638282953/1000000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((228063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c385 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((48081/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -866323/5000000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 236
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t385 : ((196021958081/5000000000000 : ℚ) : ℝ) ≤ stT249 385 := by
  have hc : ((384623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196021958081/5000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((384623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c386 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((998889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117881/10000000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 236
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t386 : ((254197533627/5000000000000 : ℚ) : ℝ) ≤ stT249 386 := by
  have hc : ((998839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254197533627/5000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((998839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c387 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((413489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1492713/10000000) (δ := 12607/1000000000) (ψ := 5473/25000) 249 236
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t387 : ((3283989503/78125000000 : ℚ) : ℝ) ≤ stT249 387 := by
  have hc : ((51683/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3283989503/78125000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((51683/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c388 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((325099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3099199/10000000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 236
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t388 : ((165018600977/10000000000000 : ℚ) : ℝ) ≤ stT249 388 := by
  have hc : ((325049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165018600977/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((325049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c389 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-304877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2350757/5000000) (δ := 12507/1000000000) (ψ := 5473/25000) 249 236
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t389 : ((-154604392467/10000000000000 : ℚ) : ℝ) ≤ stT249 389 := by
  have hc : ((-304927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154604392467/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-304927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c390 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-812887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6299721/10000000) (δ := 3149/250000000) (ψ := 5473/25000) 249 236
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t390 : ((-41164690869/1000000000000 : ℚ) : ℝ) ≤ stT249 390 := by
  have hc : ((-812937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41164690869/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-812937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c391 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-999873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1562829/2000000) (δ := 63/5000000) (ψ := 5473/25000) 249 237
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t391 : ((-252841529703/5000000000000 : ℚ) : ℝ) ≤ stT249 391 := by
  have hc : ((-999923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252841529703/5000000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-999923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c392 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-794899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6224093/10000000) (δ := 1/80000) (ψ := 5473/25000) 249 237
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t392 : ((-401510456073/10000000000000 : ℚ) : ℝ) ≤ stT249 392 := by
  have hc : ((-794949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-401510456073/10000000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-794949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c393 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-280619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4638087/10000000) (δ := 12603/1000000000) (ψ := 5473/25000) 249 237
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t393 : ((-70789493173/5000000000000 : ℚ) : ℝ) ≤ stT249 393 := by
  have hc : ((-280669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70789493173/5000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-280669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c394 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((341343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -23876/78125) (δ := 12503/1000000000) (ψ := 5473/25000) 249 237
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t394 : ((10746292691/625000000000 : ℚ) : ℝ) ≤ stT249 394 := by
  have hc : ((341293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10746292691/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((341293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c395 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((33209/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295643/2000000) (δ := 12503/1000000000) (ψ := 5473/25000) 249 237
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t395 : ((8354117439/200000000000 : ℚ) : ℝ) ≤ stT249 395 := by
  have hc : ((33207/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).1
  have hw2 : ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8354117439/200000000000 : ℚ) : ℝ)
      = ((251577/5000000 : ℚ) : ℝ) * ((33207/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c396 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((499633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2993/312500) (δ := 1/80000) (ψ := 5473/25000) 249 237
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t396 : ((15691375809/312500000000 : ℚ) : ℝ) ≤ stT249 396 := by
  have hc : ((62451/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).1
  have hw2 : ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((251259/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15691375809/312500000000 : ℚ) : ℝ)
      = ((251259/5000000 : ℚ) : ℝ) * ((62451/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c397 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((786121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1665721/10000000) (δ := 1/80000) (ψ := 5473/25000) 249 237
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t397 : ((78903448767/2000000000000 : ℚ) : ℝ) ≤ stT249 397 := by
  have hc : ((786071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78903448767/2000000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((786071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c398 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((34313/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3231807/10000000) (δ := 12603/1000000000) (ψ := 5473/25000) 249 237
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t398 : ((34392791329/2500000000000 : ℚ) : ℝ) ≤ stT249 398 := by
  have hc : ((137227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34392791329/2500000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((137227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c399 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-339859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1198477/2500000) (δ := 1/80000) (ψ := 5473/25000) 249 237
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t399 : ((-170167622943/10000000000000 : ℚ) : ℝ) ≤ stT249 399 := by
  have hc : ((-339909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170167622943/10000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-339909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c400 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-206227/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794011/1250000) (δ := 12503/1000000000) (ψ := 5473/25000) 249 237
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t400 : ((-206239912479/5000000000000 : ℚ) : ℝ) ≤ stT249 400 := by
  have hc : ((-412479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206239912479/5000000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-412479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c401 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-49989/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1560311/2000000) (δ := 1251/100000000) (ψ := 5473/25000) 249 238
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t401 : ((-49929210591/1000000000000 : ℚ) : ℝ) ≤ stT249 401 := by
  have hc : ((-99983/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).2
  have h0 : (0:ℝ) ≤ ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49929210591/1000000000000 : ℚ) : ℝ)
      = ((499377/10000000 : ℚ) : ℝ) * ((-99983/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c402 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-801421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6251157/10000000) (δ := 12593/1000000000) (ψ := 5473/25000) 249 238
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t402 : ((-79947533721/2000000000000 : ℚ) : ℝ) ≤ stT249 402 := by
  have hc : ((-801471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79947533721/2000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-801471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c403 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-61207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -940911/2000000) (δ := 1261/100000000) (ψ := 5473/25000) 249 238
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t403 : ((-3811798939/250000000000 : ℚ) : ℝ) ≤ stT249 403 := by
  have hc : ((-61217/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3811798939/250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-61217/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c404 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((150657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1580907/5000000) (δ := 12593/1000000000) (ψ := 5473/25000) 249 238
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t404 : ((4683883211/312500000000 : ℚ) : ℝ) ≤ stT249 404 := by
  have hc : ((18829/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4683883211/312500000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((18829/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c405 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((796599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1622869/10000000) (δ := 1251/100000000) (ψ := 5473/25000) 249 238
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t405 : ((395807587747/10000000000000 : ℚ) : ℝ) ≤ stT249 405 := by
  have hc : ((796549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((395807587747/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((796549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c406 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((124923/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43861/5000000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 238
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t406 : ((247980235097/5000000000000 : ℚ) : ℝ) ≤ stT249 406 := by
  have hc : ((499667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247980235097/5000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((499667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c407 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((837857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360907/2500000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 238
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t407 : ((415285011567/10000000000000 : ℚ) : ℝ) ≤ stT249 407 := by
  have hc : ((837807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415285011567/10000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((837807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c408 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((74611/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2971243/10000000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 238
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t408 : ((36932940873/2000000000000 : ℚ) : ℝ) ≤ stT249 408 := by
  have hc : ((74601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36932940873/2000000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((74601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c409 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-112651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4495123/10000000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 238
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t409 : ((-13928697261/1250000000000 : ℚ) : ℝ) ≤ stT249 409 := by
  have hc : ((-28169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13928697261/1250000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-28169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c410 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-148301/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1503817/2500000) (δ := 12493/1000000000) (ψ := 5473/25000) 249 238
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t410 : ((-14649122403/400000000000 : ℚ) : ℝ) ≤ stT249 410 := by
  have hc : ((-148311/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14649122403/400000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-148311/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c411 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-123963/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 376587/500000) (δ := 12593/1000000000) (ψ := 5473/25000) 249 238
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t411 : ((-15287392033/312500000000 : ℚ) : ℝ) ≤ stT249 411 := by
  have hc : ((-495877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15287392033/312500000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-495877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c412 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-111093/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3331743/5000000) (δ := 6293/500000000) (ψ := 5473/25000) 249 239
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t412 : ((-43787769601/1000000000000 : ℚ) : ℝ) ≤ stT249 412 := by
  have hc : ((-444397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43787769601/1000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-444397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c413 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-471483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5154421/10000000) (δ := 12517/1000000000) (ψ := 5473/25000) 249 239
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t413 : ((-58006575061/2500000000000 : ℚ) : ℝ) ≤ stT249 413 := by
  have hc : ((-471533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58006575061/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-471533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c414 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((5549/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3648967/10000000) (δ := 12517/1000000000) (ψ := 5473/25000) 249 239
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t414 : ((5451909989/1000000000000 : ℚ) : ℝ) ≤ stT249 414 := by
  have hc : ((11093/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5451909989/1000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((11093/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c415 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((653309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -536781/2500000) (δ := 6293/500000000) (ψ := 5473/25000) 249 239
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t415 : ((501049653/15625000000 : ℚ) : ℝ) ≤ stT249 415 := by
  have hc : ((653259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501049653/15625000000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((653259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c416 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((483249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -648953/10000000) (δ := 6243/500000000) (ψ := 5473/25000) 249 239
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t416 : ((2961498687/62500000000 : ℚ) : ℝ) ≤ stT249 416 := by
  have hc : ((60403/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2961498687/62500000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((60403/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c417 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((943331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84567/1000000) (δ := 12617/1000000000) (ψ := 5473/25000) 249 239
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t417 : ((230963296131/5000000000000 : ℚ) : ℝ) ≤ stT249 417 := by
  have hc : ((943281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230963296131/5000000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((943281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c418 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((297041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1168341/5000000) (δ := 12617/1000000000) (ψ := 5473/25000) 249 239
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t418 : ((3631874521/125000000000 : ℚ) : ℝ) ≤ stT249 418 := by
  have hc : ((37127/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3631874521/125000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((37127/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c419 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((41127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 764829/2000000) (δ := 6293/500000000) (ψ := 5473/25000) 249 239
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t419 : ((20067387887/10000000000000 : ℚ) : ℝ) ≤ stT249 419 := by
  have hc : ((41077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20067387887/10000000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((41077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c420 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-131189/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5308061/10000000) (δ := 12517/1000000000) (ψ := 5473/25000) 249 239
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t420 : ((-128039806253/5000000000000 : ℚ) : ℝ) ≤ stT249 420 := by
  have hc : ((-262403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128039806253/5000000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-262403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c421 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-455267/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1697107/2500000) (δ := 6243/500000000) (ψ := 5473/25000) 249 239
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t421 : ((-55474029333/1250000000000 : ℚ) : ℝ) ≤ stT249 421 := by
  have hc : ((-113823/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55474029333/1250000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-113823/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c422 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-197299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3721327/5000000) (δ := 6239/500000000) (ψ := 5473/25000) 249 240
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t422 : ((-96048640037/2000000000000 : ℚ) : ℝ) ≤ stT249 422 := by
  have hc : ((-197309/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).2
  have h0 : (0:ℝ) ≤ ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96048640037/2000000000000 : ℚ) : ℝ)
      = ((486793/10000000 : ℚ) : ℝ) * ((-197309/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c423 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-729049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5969321/10000000) (δ := 6239/500000000) (ψ := 5473/25000) 249 240
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t423 : ((-354500328483/10000000000000 : ℚ) : ℝ) ≤ stT249 423 := by
  have hc : ((-729099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).2
  have h0 : (0:ℝ) ≤ ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354500328483/10000000000000 : ℚ) : ℝ)
      = ((486217/10000000 : ℚ) : ℝ) * ((-729099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c424 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-226973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1124853/2500000) (δ := 6289/500000000) (ψ := 5473/25000) 249 240
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t424 : ((-110252130789/10000000000000 : ℚ) : ℝ) ≤ stT249 424 := by
  have hc : ((-227023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110252130789/10000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-227023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c425 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((87507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -758247/2500000) (δ := 101/8000000) (ψ := 5473/25000) 249 240
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t425 : ((84882089219/5000000000000 : ℚ) : ℝ) ≤ stT249 425 := by
  have hc : ((174989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84882089219/5000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((174989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c426 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((809207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1569989/10000000) (δ := 6239/500000000) (ψ := 5473/25000) 249 240
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t426 : ((392037375657/10000000000000 : ℚ) : ℝ) ≤ stT249 426 := by
  have hc : ((809157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392037375657/10000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((809157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c427 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((39961/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110413/10000000) (δ := 501/40000000) (ψ := 5473/25000) 249 240
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t427 : ((19337478747/400000000000 : ℚ) : ℝ) ≤ stT249 427 := by
  have hc : ((39959/40000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).1
  have hw2 : ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((483933/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19337478747/400000000000 : ℚ) : ℝ)
      = ((483933/10000000 : ℚ) : ℝ) * ((39959/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c428 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((214649/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345677/10000000) (δ := 101/8000000) (ψ := 5473/25000) 249 240
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t428 : ((25937103933/625000000000 : ℚ) : ℝ) ≤ stT249 428 := by
  have hc : ((429273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).1
  have hw2 : ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25937103933/625000000000 : ℚ) : ℝ)
      = ((60421/1250000 : ℚ) : ℝ) * ((429273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c429 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((218117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2798467/10000000) (δ := 6239/500000000) (ψ := 5473/25000) 249 240
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t429 : ((6580980623/312500000000 : ℚ) : ℝ) ≤ stT249 429 := by
  have hc : ((54523/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).1
  have hw2 : ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((120701/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6580980623/312500000000 : ℚ) : ℝ)
      = ((120701/2500000 : ℚ) : ℝ) * ((54523/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c430 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-25597/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2123917/5000000) (δ := 501/40000000) (ψ := 5473/25000) 249 240
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t430 : ((-12348796501/2000000000000 : ℚ) : ℝ) ≤ stT249 430 := by
  have hc : ((-25607/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12348796501/2000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-25607/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c431 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-649339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5693777/10000000) (δ := 501/40000000) (ψ := 5473/25000) 249 240
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t431 : ((-78200072769/2500000000000 : ℚ) : ℝ) ≤ stT249 431 := by
  have hc : ((-649389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78200072769/2500000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-649389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c432 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-959091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7136421/10000000) (δ := 101/8000000) (ψ := 5473/25000) 249 240
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t432 : ((-230733836383/5000000000000 : ℚ) : ℝ) ≤ stT249 432 := by
  have hc : ((-959141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230733836383/5000000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-959141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c433 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-958611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3566099/5000000) (δ := 3133/250000000) (ψ := 5473/25000) 249 241
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t433 : ((-46070371677/1000000000000 : ℚ) : ℝ) ≤ stT249 433 := by
  have hc : ((-958661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).2
  have h0 : (0:ℝ) ≤ ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46070371677/1000000000000 : ℚ) : ℝ)
      = ((48057/1000000 : ℚ) : ℝ) * ((-958661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c434 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-4063/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139243/2000000) (δ := 3133/250000000) (ψ := 5473/25000) 249 241
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t434 : ((-1950455013/62500000000 : ℚ) : ℝ) ≤ stT249 434 := by
  have hc : ((-65013/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).2
  have h0 : (0:ℝ) ≤ ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1950455013/62500000000 : ℚ) : ℝ)
      = ((30001/625000 : ℚ) : ℝ) * ((-65013/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c435 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-13421/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4263531/10000000) (δ := 1579/125000000) (ψ := 5473/25000) 249 241
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t435 : ((-402330229/62500000000 : ℚ) : ℝ) ≤ stT249 435 := by
  have hc : ((-6713/50000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402330229/62500000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-6713/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c436 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((105837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2834147/10000000) (δ := 12471/1000000000) (ψ := 5473/25000) 249 241
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t436 : ((101361457537/5000000000000 : ℚ) : ℝ) ≤ stT249 436 := by
  have hc : ((211649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101361457537/5000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((211649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c437 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((422769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -704031/5000000) (δ := 12571/1000000000) (ψ := 5473/25000) 249 241
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t437 : ((6319547213/156250000000 : ℚ) : ℝ) ≤ stT249 437 := by
  have hc : ((52843/62500 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6319547213/156250000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((52843/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c438 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((499991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14849/10000000) (δ := 3133/250000000) (ψ := 5473/25000) 249 241
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t438 : ((59723188547/1250000000000 : ℚ) : ℝ) ≤ stT249 438 := by
  have hc : ((249983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59723188547/1250000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((249983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c439 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((839853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71723/500000) (δ := 12471/1000000000) (ψ := 5473/25000) 249 241
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t439 : ((400815297219/10000000000000 : ℚ) : ℝ) ≤ stT249 439 := by
  have hc : ((839803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400815297219/10000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((839803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c440 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((417291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1425417/5000000) (δ := 12571/1000000000) (ψ := 5473/25000) 249 241
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t440 : ((198911719171/10000000000000 : ℚ) : ℝ) ≤ stT249 440 := by
  have hc : ((417241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198911719171/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((417241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c441 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-26877/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1065993/2500000) (δ := 1579/125000000) (ψ := 5473/25000) 249 241
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t441 : ((-12803347417/2000000000000 : ℚ) : ℝ) ≤ stT249 441 := by
  have hc : ((-26887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12803347417/2000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-26887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c442 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-321641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2836967/5000000) (δ := 12471/1000000000) (ψ := 5473/25000) 249 241
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t442 : ((-19125134529/625000000000 : ℚ) : ℝ) ≤ stT249 442 := by
  have hc : ((-160833/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19125134529/625000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-160833/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c443 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-476273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3540361/5000000) (δ := 3133/250000000) (ψ := 5473/25000) 249 241
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t443 : ((-22629632427/500000000000 : ℚ) : ℝ) ≤ stT249 443 := by
  have hc : ((-238149/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22629632427/500000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-238149/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c444 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-48419/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1805907/2500000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 242
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t444 : ((-45959654097/1000000000000 : ℚ) : ℝ) ≤ stT249 444 := by
  have hc : ((-96843/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45959654097/1000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-96843/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c445 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-687819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -582319/1000000) (δ := 12539/1000000000) (ψ := 5473/25000) 249 242
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t445 : ((-163040773987/5000000000000 : ℚ) : ℝ) ≤ stT249 445 := by
  have hc : ((-687869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163040773987/5000000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-687869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c446 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-49557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553233/1250000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 242
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t446 : ((-23471852223/2500000000000 : ℚ) : ℝ) ≤ stT249 446 := by
  have hc : ((-99139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23471852223/2500000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-99139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c447 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((175253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3031713/10000000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 242
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t447 : ((20719966281/1250000000000 : ℚ) : ℝ) ≤ stT249 447 := by
  have hc : ((43807/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20719966281/1250000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((43807/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c448 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((792289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1640613/10000000) (δ := 3141/250000000) (ψ := 5473/25000) 249 242
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t448 : ((74859455349/2000000000000 : ℚ) : ℝ) ≤ stT249 448 := by
  have hc : ((792239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74859455349/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((792239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c449 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((62181/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252687/10000000) (δ := 3141/250000000) (ψ := 5473/25000) 249 242
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t449 : ((234748338967/5000000000000 : ℚ) : ℝ) ≤ stT249 449 := by
  have hc : ((497423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234748338967/5000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((497423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c450 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((899193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1132189/10000000) (δ := 779/62500000) (ψ := 5473/25000) 249 242
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t450 : ((105964901693/2500000000000 : ℚ) : ℝ) ≤ stT249 450 := by
  have hc : ((899143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105964901693/2500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((899143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c451 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((535577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502803/2000000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 242
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t451 : ((252169489287/10000000000000 : ℚ) : ℝ) ≤ stT249 451 := by
  have hc : ((535527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252169489287/10000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((535527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c452 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((2741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 486591/1250000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 242
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t452 : ((32113829/50000000000 : ℚ) : ℝ) ≤ stT249 452 := by
  have hc : ((2731/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32113829/50000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((2731/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c453 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-127801/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5268453/10000000) (δ := 12639/1000000000) (ψ := 5473/25000) 249 242
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t453 : ((-120104045307/5000000000000 : ℚ) : ℝ) ≤ stT249 453 := by
  have hc : ((-255627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120104045307/5000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-255627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c454 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-884597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1328213/2000000) (δ := 779/62500000) (ψ := 5473/25000) 249 242
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t454 : ((-103796517157/2500000000000 : ℚ) : ℝ) ≤ stT249 454 := by
  have hc : ((-884647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103796517157/2500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-884647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c455 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-499017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7697211/10000000) (δ := 6323/500000000) (ψ := 5473/25000) 249 243
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t455 : ((-14622180121/312500000000 : ℚ) : ℝ) ≤ stT249 455 := by
  have hc : ((-249521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14622180121/312500000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-249521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c456 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-820013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253223/400000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 243
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t456 : ((-384029762459/10000000000000 : ℚ) : ℝ) ≤ stT249 456 := by
  have hc : ((-820063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384029762459/10000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-820063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c457 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-50513/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4966989/10000000) (δ := 12557/1000000000) (ψ := 5473/25000) 249 243
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t457 : ((-94527781137/5000000000000 : ℚ) : ℝ) ≤ stT249 457 := by
  have hc : ((-202077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94527781137/5000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-202077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c458 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((63957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450791/1250000) (δ := 6273/500000000) (ψ := 5473/25000) 249 243
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t458 : ((7468360427/1250000000000 : ℚ) : ℝ) ≤ stT249 458 := by
  have hc : ((15983/125000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7468360427/1250000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((15983/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c459 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((622051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2248593/10000000) (δ := 6323/500000000) (ψ := 5473/25000) 249 243
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t459 : ((7258129669/250000000000 : ℚ) : ℝ) ≤ stT249 459 := by
  have hc : ((622001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7258129669/250000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((622001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c460 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((58547/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893909/10000000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 243
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t460 : ((54592397613/1250000000000 : ℚ) : ℝ) ≤ stT249 460 := by
  have hc : ((468351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54592397613/1250000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((468351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c461 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((122909/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57239/1250000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 243
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t461 : ((114482928403/2500000000000 : ℚ) : ℝ) ≤ stT249 461 := by
  have hc : ((491611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114482928403/2500000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((491611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c462 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((93753/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 361349/2000000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 243
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t462 : ((87229850927/2500000000000 : ℚ) : ℝ) ≤ stT249 462 := by
  have hc : ((374987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87229850927/2500000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((374987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c463 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((304783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 630543/2000000) (δ := 6323/500000000) (ψ := 5473/25000) 249 243
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t463 : ((141621309687/10000000000000 : ℚ) : ℝ) ≤ stT249 463 := by
  have hc : ((304733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141621309687/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((304733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c464 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-225549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2247879/5000000) (δ := 12557/1000000000) (ψ := 5473/25000) 249 243
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t464 : ((-104731854161/10000000000000 : ℚ) : ℝ) ≤ stT249 464 := by
  have hc : ((-225599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104731854161/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-225599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c465 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-691511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5835939/10000000) (δ := 6323/500000000) (ψ := 5473/25000) 249 243
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t465 : ((-320703806579/10000000000000 : ℚ) : ℝ) ≤ stT249 465 := by
  have hc : ((-691561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320703806579/10000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-691561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c466 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-963151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7173193/10000000) (δ := 12457/1000000000) (ψ := 5473/25000) 249 243
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t466 : ((-223097578821/5000000000000 : ℚ) : ℝ) ≤ stT249 466 := by
  have hc : ((-963201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223097578821/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-963201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c467 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-966019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7200379/10000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 244
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t467 : ((-89408719881/2000000000000 : ℚ) : ℝ) ≤ stT249 467 := by
  have hc : ((-966069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89408719881/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-966069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c468 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-700961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1467213/2500000) (δ := 251/20000000) (ψ := 5473/25000) 249 244
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t468 : ((-324043035761/10000000000000 : ℚ) : ℝ) ≤ stT249 468 := by
  have hc : ((-701011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324043035761/10000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-701011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c469 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-242803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2270063/5000000) (δ := 253/20000000) (ψ := 5473/25000) 249 244
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t469 : ((-56069657787/5000000000000 : ℚ) : ℝ) ≤ stT249 469 := by
  have hc : ((-242853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56069657787/5000000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-242853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c470 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((56249/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3214263/10000000) (δ := 251/20000000) (ψ := 5473/25000) 249 244
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t470 : ((5188216467/400000000000 : ℚ) : ℝ) ≤ stT249 470 := by
  have hc : ((56239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5188216467/400000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((56239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c471 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((90907/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1891201/10000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 244
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t471 : ((6701566893/200000000000 : ℚ) : ℝ) ≤ stT249 471 := by
  have hc : ((363603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6701566893/200000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((363603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c472 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((194807/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570941/10000000) (δ := 12453/1000000000) (ψ := 5473/25000) 249 244
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t472 : ((89662526739/2000000000000 : ℚ) : ℝ) ≤ stT249 472 := by
  have hc : ((194797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89662526739/2000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((194797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c473 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((955747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 373259/5000000) (δ := 12453/1000000000) (ψ := 5473/25000) 249 244
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t473 : ((2197147403/50000000000 : ℚ) : ℝ) ≤ stT249 473 := by
  have hc : ((955697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2197147403/50000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((955697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c474 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((42433/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1030619/5000000) (δ := 12453/1000000000) (ψ := 5473/25000) 249 244
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t474 : ((31181884857/1000000000000 : ℚ) : ℝ) ≤ stT249 474 := by
  have hc : ((339439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31181884857/1000000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((339439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c475 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((109863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3373157/10000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 244
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t475 : ((25198539689/2500000000000 : ℚ) : ℝ) ≤ stT249 475 := by
  have hc : ((54919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25198539689/2500000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((54919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c476 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-148769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2341137/5000000) (δ := 251/20000000) (ψ := 5473/25000) 249 244
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t476 : ((-681997299/50000000000 : ℚ) : ℝ) ≤ stT249 476 := by
  have hc : ((-74397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-681997299/50000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-74397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c477 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-9179/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5988653/10000000) (δ := 12553/1000000000) (ψ := 5473/25000) 249 244
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t477 : ((-33624525753/1000000000000 : ℚ) : ℝ) ≤ stT249 477 := by
  have hc : ((-73437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33624525753/1000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-73437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c478 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-121859/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3646177/5000000) (δ := 253/20000000) (ψ := 5473/25000) 249 244
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t478 : ((-22295978679/500000000000 : ℚ) : ℝ) ≤ stT249 478 := by
  have hc : ((-487461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22295978679/500000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-487461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c479 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-239149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1778677/2500000) (δ := 157/12500000) (ψ := 5473/25000) 249 245
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t479 : ((-13659469911/312500000000 : ℚ) : ℝ) ≤ stT249 479 := by
  have hc : ((-478323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13659469911/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-478323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c480 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-685851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2908211/5000000) (δ := 157/12500000) (ψ := 5473/25000) 249 245
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t480 : ((-78267477209/2500000000000 : ℚ) : ℝ) ≤ stT249 480 := by
  have hc : ((-685901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78267477209/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-685901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c481 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-4707/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2260469/5000000) (δ := 12643/1000000000) (ψ := 5473/25000) 249 245
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t481 : ((-536666097/50000000000 : ℚ) : ℝ) ≤ stT249 481 := by
  have hc : ((-1177/5000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-536666097/50000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-1177/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c482 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((137971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3228067/10000000) (δ := 157/12500000) (ψ := 5473/25000) 249 245
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t482 : ((31416304851/2500000000000 : ℚ) : ℝ) ≤ stT249 482 := by
  have hc : ((68973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31416304851/2500000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((68973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c483 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((714299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121121/625000) (δ := 623/50000000) (ψ := 5473/25000) 249 245
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t483 : ((64998801747/2000000000000 : ℚ) : ℝ) ≤ stT249 483 := by
  have hc : ((714249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64998801747/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((714249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c484 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((966347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -650419/10000000) (δ := 157/12500000) (ψ := 5473/25000) 249 245
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t484 : ((87845093973/2000000000000 : ℚ) : ℝ) ≤ stT249 484 := by
  have hc : ((966297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87845093973/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((966297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c485 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((48399/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317179/5000000) (δ := 12643/1000000000) (ψ := 5473/25000) 249 245
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t485 : ((10987844567/250000000000 : ℚ) : ℝ) ≤ stT249 485 := by
  have hc : ((96793/100000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10987844567/250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((96793/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c486 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((2881/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239573/1250000) (δ := 623/50000000) (ψ := 5473/25000) 249 245
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t486 : ((1633446009/50000000000 : ℚ) : ℝ) ≤ stT249 486 := by
  have hc : ((3601/5000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1633446009/50000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((3601/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c487 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((288197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3196133/10000000) (δ := 157/12500000) (ψ := 5473/25000) 249 245
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t487 : ((130571796021/10000000000000 : ℚ) : ℝ) ≤ stT249 487 := by
  have hc : ((288147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130571796021/10000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((288147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c488 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-108349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4473067/10000000) (δ := 623/50000000) (ψ := 5473/25000) 249 245
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t488 : ((-24529316973/2500000000000 : ℚ) : ℝ) ≤ stT249 488 := by
  have hc : ((-54187/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24529316973/2500000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-54187/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c489 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-665477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1436831/2500000) (δ := 12643/1000000000) (ψ := 5473/25000) 249 245
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t489 : ((-37620244729/1250000000000 : ℚ) : ℝ) ≤ stT249 489 := by
  have hc : ((-665527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37620244729/1250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-665527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c490 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-188949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701903/1000000) (δ := 157/12500000) (ψ := 5473/25000) 249 245
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t490 : ((-42681492043/1000000000000 : ℚ) : ℝ) ≤ stT249 490 := by
  have hc : ((-188959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42681492043/1000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-188959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c491 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-196991/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7419781/10000000) (δ := 2527/200000000) (ψ := 5473/25000) 249 246
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t491 : ((-44452684647/1000000000000 : ℚ) : ℝ) ≤ stT249 491 := by
  have hc : ((-197001/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44452684647/1000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-197001/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c492 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-777387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3076621/5000000) (δ := 3117/250000000) (ψ := 5473/25000) 249 246
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t492 : ((-70099161979/2000000000000 : ℚ) : ℝ) ≤ stT249 492 := by
  have hc : ((-777437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70099161979/2000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-777437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c493 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((-75099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2444659/5000000) (δ := 3117/250000000) (ψ := 5473/25000) 249 246
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t493 : ((-16913720601/1000000000000 : ℚ) : ℝ) ≤ stT249 493 := by
  have hc : ((-75109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16913720601/1000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-75109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c494 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((119357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -906971/2500000) (δ := 3117/250000000) (ψ := 5473/25000) 249 246
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t494 : ((53678724747/10000000000000 : ℚ) : ℝ) ≤ stT249 494 := by
  have hc : ((119307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53678724747/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((119307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c495 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((145903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -473813/2000000) (δ := 2527/200000000) (ψ := 5473/25000) 249 246
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t495 : ((65572819473/2500000000000 : ℚ) : ℝ) ≤ stT249 495 := by
  have hc : ((291781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65572819473/2500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((291781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c496 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((90257/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222547/2000000) (δ := 3117/250000000) (ψ := 5473/25000) 249 246
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t496 : ((10131080319/250000000000 : ℚ) : ℝ) ≤ stT249 496 := by
  have hc : ((22563/25000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10131080319/250000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((22563/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c497 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((998409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70521/5000000) (δ := 2507/200000000) (ψ := 5473/25000) 249 246
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t497 : ((447824911399/10000000000000 : ℚ) : ℝ) ≤ stT249 497 := by
  have hc : ((998359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((447824911399/10000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((998359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c498 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((424447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1392267/10000000) (δ := 2507/200000000) (ψ := 5473/25000) 249 246
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t498 : ((9509387121/250000000000 : ℚ) : ℝ) ≤ stT249 498 := by
  have hc : ((212211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9509387121/250000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((212211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c499 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((492009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1320501/5000000) (δ := 2507/200000000) (ψ := 5473/25000) 249 246
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t499 : ((220230857899/10000000000000 : ℚ) : ℝ) ≤ stT249 499 := by
  have hc : ((491959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).1
  have hw2 : ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220230857899/10000000000000 : ℚ) : ℝ)
      = ((447661/10000000 : ℚ) : ℝ) * ((491959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_c500 :
    |Real.cos (((249 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((15897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3887247/10000000) (δ := 2507/200000000) (ψ := 5473/25000) 249 246
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st249_t500 : ((7086984411/10000000000000 : ℚ) : ℝ) ≤ stT249 500 := by
  have hc : ((15847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((249 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((5473/25000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st249_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7086984411/10000000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((15847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st249_p1 : ((976083/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT249 (i+1) := by
  rw [Finset.sum_range_one]
  exact st249_t1

theorem st249_p2 : ((820895804893/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT249 (i+1))
      = (∑ i ∈ Finset.range 1, stT249 (i+1)) + stT249 2 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 1
    simpa using h
  have hprev := st249_p1
  have hstep := st249_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p3 : ((-1244688535573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT249 (i+1))
      = (∑ i ∈ Finset.range 2, stT249 (i+1)) + stT249 3 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 2
    simpa using h
  have hprev := st249_p2
  have hstep := st249_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p4 : ((808851464427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT249 (i+1))
      = (∑ i ∈ Finset.range 3, stT249 (i+1)) + stT249 4 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 3
    simpa using h
  have hprev := st249_p3
  have hstep := st249_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p5 : ((759698217651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT249 (i+1))
      = (∑ i ∈ Finset.range 4, stT249 (i+1)) + stT249 5 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 4
    simpa using h
  have hprev := st249_p4
  have hstep := st249_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p6 : ((1384477506211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT249 (i+1))
      = (∑ i ∈ Finset.range 5, stT249 (i+1)) + stT249 6 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 5
    simpa using h
  have hprev := st249_p5
  have hstep := st249_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p7 : ((2210274915373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT249 (i+1))
      = (∑ i ∈ Finset.range 6, stT249 (i+1)) + stT249 7 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 6
    simpa using h
  have hprev := st249_p6
  have hstep := st249_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p8 : ((797453191919/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT249 (i+1))
      = (∑ i ∈ Finset.range 7, stT249 (i+1)) + stT249 8 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 7
    simpa using h
  have hprev := st249_p7
  have hstep := st249_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p9 : ((2401696303159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT249 (i+1))
      = (∑ i ∈ Finset.range 8, stT249 (i+1)) + stT249 9 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 8
    simpa using h
  have hprev := st249_p8
  have hstep := st249_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p10 : ((10284078538219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT249 (i+1))
      = (∑ i ∈ Finset.range 9, stT249 (i+1)) + stT249 10 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 9
    simpa using h
  have hprev := st249_p9
  have hstep := st249_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p11 : ((13295905065049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT249 (i+1))
      = (∑ i ∈ Finset.range 10, stT249 (i+1)) + stT249 11 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 10
    simpa using h
  have hprev := st249_p10
  have hstep := st249_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p12 : ((10605322297209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT249 (i+1))
      = (∑ i ∈ Finset.range 11, stT249 (i+1)) + stT249 12 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 11
    simpa using h
  have hprev := st249_p11
  have hstep := st249_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p13 : ((8502154300901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT249 (i+1))
      = (∑ i ∈ Finset.range 12, stT249 (i+1)) + stT249 13 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 12
    simpa using h
  have hprev := st249_p12
  have hstep := st249_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p14 : ((2979834077629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT249 (i+1))
      = (∑ i ∈ Finset.range 13, stT249 (i+1)) + stT249 14 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 13
    simpa using h
  have hprev := st249_p13
  have hstep := st249_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p15 : ((5411282093537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT249 (i+1))
      = (∑ i ∈ Finset.range 14, stT249 (i+1)) + stT249 15 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 14
    simpa using h
  have hprev := st249_p14
  have hstep := st249_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p16 : ((6773032093537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT249 (i+1))
      = (∑ i ∈ Finset.range 15, stT249 (i+1)) + stT249 16 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 15
    simpa using h
  have hprev := st249_p15
  have hstep := st249_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p17 : ((6861045837421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT249 (i+1))
      = (∑ i ∈ Finset.range 16, stT249 (i+1)) + stT249 17 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 16
    simpa using h
  have hprev := st249_p16
  have hstep := st249_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p18 : ((4507996778199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT249 (i+1))
      = (∑ i ∈ Finset.range 17, stT249 (i+1)) + stT249 18 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 17
    simpa using h
  have hprev := st249_p17
  have hstep := st249_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p19 : ((3183299477523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT249 (i+1))
      = (∑ i ∈ Finset.range 18, stT249 (i+1)) + stT249 19 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 18
    simpa using h
  have hprev := st249_p18
  have hstep := st249_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p20 : ((2292188366367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT249 (i+1))
      = (∑ i ∈ Finset.range 19, stT249 (i+1)) + stT249 20 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 19
    simpa using h
  have hprev := st249_p19
  have hstep := st249_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p21 : ((685532891469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT249 (i+1))
      = (∑ i ∈ Finset.range 20, stT249 (i+1)) + stT249 21 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 20
    simpa using h
  have hprev := st249_p20
  have hstep := st249_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p22 : ((-1385702220491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT249 (i+1))
      = (∑ i ∈ Finset.range 21, stT249 (i+1)) + stT249 22 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 21
    simpa using h
  have hprev := st249_p21
  have hstep := st249_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p23 : ((-1039972834427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT249 (i+1))
      = (∑ i ∈ Finset.range 22, stT249 (i+1)) + stT249 23 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 22
    simpa using h
  have hprev := st249_p22
  have hstep := st249_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p24 : ((684087891547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT249 (i+1))
      = (∑ i ∈ Finset.range 23, stT249 (i+1)) + stT249 24 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 23
    simpa using h
  have hprev := st249_p23
  have hstep := st249_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p25 : ((-1285453093223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT249 (i+1))
      = (∑ i ∈ Finset.range 24, stT249 (i+1)) + stT249 25 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 24
    simpa using h
  have hprev := st249_p24
  have hstep := st249_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p26 : ((4200568423/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT249 (i+1))
      = (∑ i ∈ Finset.range 25, stT249 (i+1)) + stT249 26 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 25
    simpa using h
  have hprev := st249_p25
  have hstep := st249_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p27 : ((-63960028033/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT249 (i+1))
      = (∑ i ∈ Finset.range 26, stT249 (i+1)) + stT249 27 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 26
    simpa using h
  have hprev := st249_p26
  have hstep := st249_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p28 : ((149259349701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT249 (i+1))
      = (∑ i ∈ Finset.range 27, stT249 (i+1)) + stT249 28 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 27
    simpa using h
  have hprev := st249_p27
  have hstep := st249_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p29 : ((-121116952913/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT249 (i+1))
      = (∑ i ∈ Finset.range 28, stT249 (i+1)) + stT249 29 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 28
    simpa using h
  have hprev := st249_p28
  have hstep := st249_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p30 : ((-186502783219/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT249 (i+1))
      = (∑ i ∈ Finset.range 29, stT249 (i+1)) + stT249 30 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 29
    simpa using h
  have hprev := st249_p29
  have hstep := st249_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p31 : ((766128353397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT249 (i+1))
      = (∑ i ∈ Finset.range 30, stT249 (i+1)) + stT249 31 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 30
    simpa using h
  have hprev := st249_p30
  have hstep := st249_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p32 : ((106814902009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT249 (i+1))
      = (∑ i ∈ Finset.range 31, stT249 (i+1)) + stT249 32 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 31
    simpa using h
  have hprev := st249_p31
  have hstep := st249_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p33 : ((-1602624630437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT249 (i+1))
      = (∑ i ∈ Finset.range 32, stT249 (i+1)) + stT249 33 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 32
    simpa using h
  have hprev := st249_p32
  have hstep := st249_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p34 : ((-1994173084097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT249 (i+1))
      = (∑ i ∈ Finset.range 33, stT249 (i+1)) + stT249 34 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 33
    simpa using h
  have hprev := st249_p33
  have hstep := st249_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p35 : ((-899637803009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT249 (i+1))
      = (∑ i ∈ Finset.range 34, stT249 (i+1)) + stT249 35 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 34
    simpa using h
  have hprev := st249_p34
  have hstep := st249_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p36 : ((30071061457/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT249 (i+1))
      = (∑ i ∈ Finset.range 35, stT249 (i+1)) + stT249 36 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 35
    simpa using h
  have hprev := st249_p35
  have hstep := st249_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p37 : ((70726207849/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT249 (i+1))
      = (∑ i ∈ Finset.range 36, stT249 (i+1)) + stT249 37 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 36
    simpa using h
  have hprev := st249_p36
  have hstep := st249_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p38 : ((1718744805283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT249 (i+1))
      = (∑ i ∈ Finset.range 37, stT249 (i+1)) + stT249 38 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 37
    simpa using h
  have hprev := st249_p37
  have hstep := st249_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p39 : ((2186984990179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT249 (i+1))
      = (∑ i ∈ Finset.range 38, stT249 (i+1)) + stT249 39 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 38
    simpa using h
  have hprev := st249_p38
  have hstep := st249_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p40 : ((1317901435007/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT249 (i+1))
      = (∑ i ∈ Finset.range 39, stT249 (i+1)) + stT249 40 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 39
    simpa using h
  have hprev := st249_p39
  have hstep := st249_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p41 : ((1264574989189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT249 (i+1))
      = (∑ i ∈ Finset.range 40, stT249 (i+1)) + stT249 41 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 40
    simpa using h
  have hprev := st249_p40
  have hstep := st249_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p42 : ((3819378257491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT249 (i+1))
      = (∑ i ∈ Finset.range 41, stT249 (i+1)) + stT249 42 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 41
    simpa using h
  have hprev := st249_p41
  have hstep := st249_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p43 : ((9151707858347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT249 (i+1))
      = (∑ i ∈ Finset.range 42, stT249 (i+1)) + stT249 43 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 42
    simpa using h
  have hprev := st249_p42
  have hstep := st249_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p44 : ((10519745580771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT249 (i+1))
      = (∑ i ∈ Finset.range 43, stT249 (i+1)) + stT249 44 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 43
    simpa using h
  have hprev := st249_p43
  have hstep := st249_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p45 : ((11167870946507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT249 (i+1))
      = (∑ i ∈ Finset.range 44, stT249 (i+1)) + stT249 45 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 44
    simpa using h
  have hprev := st249_p44
  have hstep := st249_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p46 : ((10647577616907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT249 (i+1))
      = (∑ i ∈ Finset.range 45, stT249 (i+1)) + stT249 46 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 45
    simpa using h
  have hprev := st249_p45
  have hstep := st249_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p47 : ((9246504908357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT249 (i+1))
      = (∑ i ∈ Finset.range 46, stT249 (i+1)) + stT249 47 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 46
    simpa using h
  have hprev := st249_p46
  have hstep := st249_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p48 : ((8199032511397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT249 (i+1))
      = (∑ i ∈ Finset.range 47, stT249 (i+1)) + stT249 48 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 47
    simpa using h
  have hprev := st249_p47
  have hstep := st249_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p49 : ((346853751931/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT249 (i+1))
      = (∑ i ∈ Finset.range 48, stT249 (i+1)) + stT249 49 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 48
    simpa using h
  have hprev := st249_p48
  have hstep := st249_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p50 : ((5042616471749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT249 (i+1))
      = (∑ i ∈ Finset.range 49, stT249 (i+1)) + stT249 50 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 49
    simpa using h
  have hprev := st249_p49
  have hstep := st249_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p51 : ((5181372317369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT249 (i+1))
      = (∑ i ∈ Finset.range 50, stT249 (i+1)) + stT249 51 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 50
    simpa using h
  have hprev := st249_p50
  have hstep := st249_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p52 : ((904731701217/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT249 (i+1))
      = (∑ i ∈ Finset.range 51, stT249 (i+1)) + stT249 52 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 51
    simpa using h
  have hprev := st249_p51
  have hstep := st249_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p53 : ((2143130120757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT249 (i+1))
      = (∑ i ∈ Finset.range 52, stT249 (i+1)) + stT249 53 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 52
    simpa using h
  have hprev := st249_p52
  have hstep := st249_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p54 : ((4937281239141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT249 (i+1))
      = (∑ i ∈ Finset.range 53, stT249 (i+1)) + stT249 54 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 53
    simpa using h
  have hprev := st249_p53
  have hstep := st249_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p55 : ((10077818795143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT249 (i+1))
      = (∑ i ∈ Finset.range 54, stT249 (i+1)) + stT249 55 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 54
    simpa using h
  have hprev := st249_p54
  have hstep := st249_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p56 : ((8745143877569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT249 (i+1))
      = (∑ i ∈ Finset.range 55, stT249 (i+1)) + stT249 56 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 55
    simpa using h
  have hprev := st249_p55
  have hstep := st249_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p57 : ((1847177391433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT249 (i+1))
      = (∑ i ∈ Finset.range 56, stT249 (i+1)) + stT249 57 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 56
    simpa using h
  have hprev := st249_p56
  have hstep := st249_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p58 : ((10186278741173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT249 (i+1))
      = (∑ i ∈ Finset.range 57, stT249 (i+1)) + stT249 58 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 57
    simpa using h
  have hprev := st249_p57
  have hstep := st249_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p59 : ((8964814297813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT249 (i+1))
      = (∑ i ∈ Finset.range 58, stT249 (i+1)) + stT249 59 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 58
    simpa using h
  have hprev := st249_p58
  have hstep := st249_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p60 : ((9188178206711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT249 (i+1))
      = (∑ i ∈ Finset.range 59, stT249 (i+1)) + stT249 60 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 59
    simpa using h
  have hprev := st249_p59
  have hstep := st249_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p61 : ((10106825601927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT249 (i+1))
      = (∑ i ∈ Finset.range 60, stT249 (i+1)) + stT249 61 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 60
    simpa using h
  have hprev := st249_p60
  have hstep := st249_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p62 : ((1769722860099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT249 (i+1))
      = (∑ i ∈ Finset.range 61, stT249 (i+1)) + stT249 62 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 61
    simpa using h
  have hprev := st249_p61
  have hstep := st249_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p63 : ((9551126465857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT249 (i+1))
      = (∑ i ∈ Finset.range 62, stT249 (i+1)) + stT249 63 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 62
    simpa using h
  have hprev := st249_p62
  have hstep := st249_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p64 : ((9784902715857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT249 (i+1))
      = (∑ i ∈ Finset.range 63, stT249 (i+1)) + stT249 64 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 63
    simpa using h
  have hprev := st249_p63
  have hstep := st249_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p65 : ((8807767724589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT249 (i+1))
      = (∑ i ∈ Finset.range 64, stT249 (i+1)) + stT249 65 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 64
    simpa using h
  have hprev := st249_p64
  have hstep := st249_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p66 : ((10038611562491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT249 (i+1))
      = (∑ i ∈ Finset.range 65, stT249 (i+1)) + stT249 66 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 65
    simpa using h
  have hprev := st249_p65
  have hstep := st249_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p67 : ((4514844092693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT249 (i+1))
      = (∑ i ∈ Finset.range 66, stT249 (i+1)) + stT249 67 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 66
    simpa using h
  have hprev := st249_p66
  have hstep := st249_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p68 : ((4764396247601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT249 (i+1))
      = (∑ i ∈ Finset.range 67, stT249 (i+1)) + stT249 68 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 67
    simpa using h
  have hprev := st249_p67
  have hstep := st249_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p69 : ((4806031676531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT249 (i+1))
      = (∑ i ∈ Finset.range 68, stT249 (i+1)) + stT249 69 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 68
    simpa using h
  have hprev := st249_p68
  have hstep := st249_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p70 : ((9028030240189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT249 (i+1))
      = (∑ i ∈ Finset.range 69, stT249 (i+1)) + stT249 70 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 69
    simpa using h
  have hprev := st249_p69
  have hstep := st249_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p71 : ((9958229187989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT249 (i+1))
      = (∑ i ∈ Finset.range 70, stT249 (i+1)) + stT249 71 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 70
    simpa using h
  have hprev := st249_p70
  have hstep := st249_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p72 : ((8842851254341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT249 (i+1))
      = (∑ i ∈ Finset.range 71, stT249 (i+1)) + stT249 72 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 71
    simpa using h
  have hprev := st249_p71
  have hstep := st249_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p73 : ((2503111034263/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT249 (i+1))
      = (∑ i ∈ Finset.range 72, stT249 (i+1)) + stT249 73 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 72
    simpa using h
  have hprev := st249_p72
  have hstep := st249_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p74 : ((8875491644541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT249 (i+1))
      = (∑ i ∈ Finset.range 73, stT249 (i+1)) + stT249 74 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 73
    simpa using h
  have hprev := st249_p73
  have hstep := st249_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p75 : ((9933999361041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT249 (i+1))
      = (∑ i ∈ Finset.range 74, stT249 (i+1)) + stT249 75 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 74
    simpa using h
  have hprev := st249_p74
  have hstep := st249_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p76 : ((896661143347/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT249 (i+1))
      = (∑ i ∈ Finset.range 75, stT249 (i+1)) + stT249 76 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 75
    simpa using h
  have hprev := st249_p75
  have hstep := st249_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p77 : ((246303309547/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT249 (i+1))
      = (∑ i ∈ Finset.range 76, stT249 (i+1)) + stT249 77 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 76
    simpa using h
  have hprev := st249_p76
  have hstep := st249_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p78 : ((4512618842213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT249 (i+1))
      = (∑ i ∈ Finset.range 77, stT249 (i+1)) + stT249 78 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 77
    simpa using h
  have hprev := st249_p77
  have hstep := st249_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p79 : ((78584087993/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT249 (i+1))
      = (∑ i ∈ Finset.range 78, stT249 (i+1)) + stT249 79 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 78
    simpa using h
  have hprev := st249_p78
  have hstep := st249_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p80 : ((9022695429109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT249 (i+1))
      = (∑ i ∈ Finset.range 79, stT249 (i+1)) + stT249 80 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 79
    simpa using h
  have hprev := st249_p79
  have hstep := st249_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p81 : ((2463636336481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT249 (i+1))
      = (∑ i ∈ Finset.range 80, stT249 (i+1)) + stT249 81 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 80
    simpa using h
  have hprev := st249_p80
  have hstep := st249_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p82 : ((2241906800579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT249 (i+1))
      = (∑ i ∈ Finset.range 81, stT249 (i+1)) + stT249 82 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 81
    simpa using h
  have hprev := st249_p81
  have hstep := st249_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p83 : ((2480714184667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT249 (i+1))
      = (∑ i ∈ Finset.range 82, stT249 (i+1)) + stT249 83 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 82
    simpa using h
  have hprev := st249_p82
  have hstep := st249_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p84 : ((4449956473399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT249 (i+1))
      = (∑ i ∈ Finset.range 83, stT249 (i+1)) + stT249 84 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 83
    simpa using h
  have hprev := st249_p83
  have hstep := st249_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p85 : ((4985273994501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT249 (i+1))
      = (∑ i ∈ Finset.range 84, stT249 (i+1)) + stT249 85 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 84
    simpa using h
  have hprev := st249_p84
  have hstep := st249_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p86 : ((889470661337/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT249 (i+1))
      = (∑ i ∈ Finset.range 85, stT249 (i+1)) + stT249 86 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 85
    simpa using h
  have hprev := st249_p85
  have hstep := st249_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p87 : ((4954181389341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT249 (i+1))
      = (∑ i ∈ Finset.range 86, stT249 (i+1)) + stT249 87 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 86
    simpa using h
  have hprev := st249_p86
  have hstep := st249_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p88 : ((4522670965171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT249 (i+1))
      = (∑ i ∈ Finset.range 87, stT249 (i+1)) + stT249 88 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 87
    simpa using h
  have hprev := st249_p87
  have hstep := st249_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p89 : ((4828579739389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT249 (i+1))
      = (∑ i ∈ Finset.range 88, stT249 (i+1)) + stT249 89 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 88
    simpa using h
  have hprev := st249_p88
  have hstep := st249_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p90 : ((4695148431077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT249 (i+1))
      = (∑ i ∈ Finset.range 89, stT249 (i+1)) + stT249 90 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 89
    simpa using h
  have hprev := st249_p89
  have hstep := st249_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p91 : ((9249905293529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT249 (i+1))
      = (∑ i ∈ Finset.range 90, stT249 (i+1)) + stT249 91 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 90
    simpa using h
  have hprev := st249_p90
  have hstep := st249_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p92 : ((9798819451529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT249 (i+1))
      = (∑ i ∈ Finset.range 91, stT249 (i+1)) + stT249 92 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 91
    simpa using h
  have hprev := st249_p91
  have hstep := st249_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p93 : ((8923848686497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT249 (i+1))
      = (∑ i ∈ Finset.range 92, stT249 (i+1)) + stT249 93 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 92
    simpa using h
  have hprev := st249_p92
  have hstep := st249_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p94 : ((9951216201967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT249 (i+1))
      = (∑ i ∈ Finset.range 93, stT249 (i+1)) + stT249 94 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 93
    simpa using h
  have hprev := st249_p93
  have hstep := st249_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p95 : ((9013742254423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT249 (i+1))
      = (∑ i ∈ Finset.range 94, stT249 (i+1)) + stT249 95 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 94
    simpa using h
  have hprev := st249_p94
  have hstep := st249_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p96 : ((9605066008163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT249 (i+1))
      = (∑ i ∈ Finset.range 95, stT249 (i+1)) + stT249 96 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 95
    simpa using h
  have hprev := st249_p95
  have hstep := st249_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p97 : ((477370273369/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT249 (i+1))
      = (∑ i ∈ Finset.range 96, stT249 (i+1)) + stT249 97 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 96
    simpa using h
  have hprev := st249_p96
  have hstep := st249_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p98 : ((9035856917109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT249 (i+1))
      = (∑ i ∈ Finset.range 97, stT249 (i+1)) + stT249 98 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 97
    simpa using h
  have hprev := st249_p97
  have hstep := st249_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p99 : ((1243867260053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT249 (i+1))
      = (∑ i ∈ Finset.range 98, stT249 (i+1)) + stT249 99 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 98
    simpa using h
  have hprev := st249_p98
  have hstep := st249_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p100 : ((1121682510053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT249 (i+1))
      = (∑ i ∈ Finset.range 99, stT249 (i+1)) + stT249 100 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 99
    simpa using h
  have hprev := st249_p99
  have hstep := st249_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p101 : ((1921967795777/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT249 (i+1))
      = (∑ i ∈ Finset.range 100, stT249 (i+1)) + stT249 101 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 100
    simpa using h
  have hprev := st249_p100
  have hstep := st249_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p102 : ((9604232760909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT249 (i+1))
      = (∑ i ∈ Finset.range 101, stT249 (i+1)) + stT249 102 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 101
    simpa using h
  have hprev := st249_p101
  have hstep := st249_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p103 : ((8964372268199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT249 (i+1))
      = (∑ i ∈ Finset.range 102, stT249 (i+1)) + stT249 103 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 102
    simpa using h
  have hprev := st249_p102
  have hstep := st249_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p104 : ((9936842871599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT249 (i+1))
      = (∑ i ∈ Finset.range 103, stT249 (i+1)) + stT249 104 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 103
    simpa using h
  have hprev := st249_p103
  have hstep := st249_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p105 : ((1829703179841/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT249 (i+1))
      = (∑ i ∈ Finset.range 104, stT249 (i+1)) + stT249 105 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 104
    simpa using h
  have hprev := st249_p104
  have hstep := st249_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p106 : ((1860434637241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT249 (i+1))
      = (∑ i ∈ Finset.range 105, stT249 (i+1)) + stT249 106 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 105
    simpa using h
  have hprev := st249_p105
  have hstep := st249_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p107 : ((1976605368889/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT249 (i+1))
      = (∑ i ∈ Finset.range 106, stT249 (i+1)) + stT249 107 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 106
    simpa using h
  have hprev := st249_p106
  have hstep := st249_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p108 : ((892562077823/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT249 (i+1))
      = (∑ i ∈ Finset.range 107, stT249 (i+1)) + stT249 108 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 107
    simpa using h
  have hprev := st249_p107
  have hstep := st249_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p109 : ((4814578692397/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT249 (i+1))
      = (∑ i ∈ Finset.range 108, stT249 (i+1)) + stT249 109 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 108
    simpa using h
  have hprev := st249_p108
  have hstep := st249_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p110 : ((24174229787/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT249 (i+1))
      = (∑ i ∈ Finset.range 109, stT249 (i+1)) + stT249 110 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 109
    simpa using h
  have hprev := st249_p109
  have hstep := st249_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p111 : ((2227089748697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT249 (i+1))
      = (∑ i ∈ Finset.range 110, stT249 (i+1)) + stT249 111 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 110
    simpa using h
  have hprev := st249_p110
  have hstep := st249_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p112 : ((1963880309963/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT249 (i+1))
      = (∑ i ∈ Finset.range 111, stT249 (i+1)) + stT249 112 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 111
    simpa using h
  have hprev := st249_p111
  have hstep := st249_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p113 : ((9475489003751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT249 (i+1))
      = (∑ i ∈ Finset.range 112, stT249 (i+1)) + stT249 113 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 112
    simpa using h
  have hprev := st249_p112
  have hstep := st249_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p114 : ((8967236562061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT249 (i+1))
      = (∑ i ∈ Finset.range 113, stT249 (i+1)) + stT249 114 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 113
    simpa using h
  have hprev := st249_p113
  have hstep := st249_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p115 : ((9899264985021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT249 (i+1))
      = (∑ i ∈ Finset.range 114, stT249 (i+1)) + stT249 115 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 114
    simpa using h
  have hprev := st249_p114
  have hstep := st249_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p116 : ((9363227358611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT249 (i+1))
      = (∑ i ∈ Finset.range 115, stT249 (i+1)) + stT249 116 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 115
    simpa using h
  have hprev := st249_p115
  have hstep := st249_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p117 : ((563293405247/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT249 (i+1))
      = (∑ i ∈ Finset.range 116, stT249 (i+1)) + stT249 117 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 116
    simpa using h
  have hprev := st249_p116
  have hstep := st249_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p118 : ((4960766043013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT249 (i+1))
      = (∑ i ∈ Finset.range 117, stT249 (i+1)) + stT249 118 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 117
    simpa using h
  have hprev := st249_p117
  have hstep := st249_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p119 : ((9337973419713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT249 (i+1))
      = (∑ i ∈ Finset.range 118, stT249 (i+1)) + stT249 119 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 118
    simpa using h
  have hprev := st249_p118
  have hstep := st249_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p120 : ((9009619198239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT249 (i+1))
      = (∑ i ∈ Finset.range 119, stT249 (i+1)) + stT249 120 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 119
    simpa using h
  have hprev := st249_p119
  have hstep := st249_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p121 : ((9911259205689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT249 (i+1))
      = (∑ i ∈ Finset.range 120, stT249 (i+1)) + stT249 121 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 120
    simpa using h
  have hprev := st249_p120
  have hstep := st249_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p122 : ((9395300208279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT249 (i+1))
      = (∑ i ∈ Finset.range 121, stT249 (i+1)) + stT249 122 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 121
    simpa using h
  have hprev := st249_p121
  have hstep := st249_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p123 : ((8960904455719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT249 (i+1))
      = (∑ i ∈ Finset.range 122, stT249 (i+1)) + stT249 123 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 122
    simpa using h
  have hprev := st249_p122
  have hstep := st249_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p124 : ((9857416383883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT249 (i+1))
      = (∑ i ∈ Finset.range 123, stT249 (i+1)) + stT249 124 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 123
    simpa using h
  have hprev := st249_p123
  have hstep := st249_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p125 : ((9532254239907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT249 (i+1))
      = (∑ i ∈ Finset.range 124, stT249 (i+1)) + stT249 125 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 124
    simpa using h
  have hprev := st249_p124
  have hstep := st249_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p126 : ((890220621519/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT249 (i+1))
      = (∑ i ∈ Finset.range 125, stT249 (i+1)) + stT249 126 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 125
    simpa using h
  have hprev := st249_p125
  have hstep := st249_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p127 : ((4861791873583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT249 (i+1))
      = (∑ i ∈ Finset.range 126, stT249 (i+1)) + stT249 127 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 126
    simpa using h
  have hprev := st249_p126
  have hstep := st249_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p128 : ((1945726674149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT249 (i+1))
      = (∑ i ∈ Finset.range 127, stT249 (i+1)) + stT249 128 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 127
    simpa using h
  have hprev := st249_p127
  have hstep := st249_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p129 : ((4452476485387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT249 (i+1))
      = (∑ i ∈ Finset.range 128, stT249 (i+1)) + stT249 129 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 128
    simpa using h
  have hprev := st249_p128
  have hstep := st249_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p130 : ((4739362157187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT249 (i+1))
      = (∑ i ∈ Finset.range 129, stT249 (i+1)) + stT249 130 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 129
    simpa using h
  have hprev := st249_p129
  have hstep := st249_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p131 : ((4956532207687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT249 (i+1))
      = (∑ i ∈ Finset.range 130, stT249 (i+1)) + stT249 131 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 130
    simpa using h
  have hprev := st249_p130
  have hstep := st249_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p132 : ((4529783962543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT249 (i+1))
      = (∑ i ∈ Finset.range 131, stT249 (i+1)) + stT249 132 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 131
    simpa using h
  have hprev := st249_p131
  have hstep := st249_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p133 : ((4577729887589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT249 (i+1))
      = (∑ i ∈ Finset.range 132, stT249 (i+1)) + stT249 133 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 132
    simpa using h
  have hprev := st249_p132
  have hstep := st249_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p134 : ((4974658660427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT249 (i+1))
      = (∑ i ∈ Finset.range 133, stT249 (i+1)) + stT249 134 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 133
    simpa using h
  have hprev := st249_p133
  have hstep := st249_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p135 : ((9404258582291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT249 (i+1))
      = (∑ i ∈ Finset.range 134, stT249 (i+1)) + stT249 135 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 134
    simpa using h
  have hprev := st249_p134
  have hstep := st249_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p136 : ((8907238489631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT249 (i+1))
      = (∑ i ∈ Finset.range 135, stT249 (i+1)) + stT249 136 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 135
    simpa using h
  have hprev := st249_p135
  have hstep := st249_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p137 : ((9705332663753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT249 (i+1))
      = (∑ i ∈ Finset.range 136, stT249 (i+1)) + stT249 137 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 136
    simpa using h
  have hprev := st249_p136
  have hstep := st249_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p138 : ((9811159958417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT249 (i+1))
      = (∑ i ∈ Finset.range 137, stT249 (i+1)) + stT249 138 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 137
    simpa using h
  have hprev := st249_p137
  have hstep := st249_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p139 : ((4483684409191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT249 (i+1))
      = (∑ i ∈ Finset.range 138, stT249 (i+1)) + stT249 139 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 138
    simpa using h
  have hprev := st249_p138
  have hstep := st249_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p140 : ((23075987777/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT249 (i+1))
      = (∑ i ∈ Finset.range 139, stT249 (i+1)) + stT249 140 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 139
    simpa using h
  have hprev := st249_p139
  have hstep := st249_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p141 : ((498101952829/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT249 (i+1))
      = (∑ i ∈ Finset.range 140, stT249 (i+1)) + stT249 141 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 140
    simpa using h
  have hprev := st249_p140
  have hstep := st249_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p142 : ((4708483005651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT249 (i+1))
      = (∑ i ∈ Finset.range 141, stT249 (i+1)) + stT249 142 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 141
    simpa using h
  have hprev := st249_p141
  have hstep := st249_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p143 : ((8886360629129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT249 (i+1))
      = (∑ i ∈ Finset.range 142, stT249 (i+1)) + stT249 143 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 142
    simpa using h
  have hprev := st249_p142
  have hstep := st249_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p144 : ((2402071543423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT249 (i+1))
      = (∑ i ∈ Finset.range 143, stT249 (i+1)) + stT249 144 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 143
    simpa using h
  have hprev := st249_p143
  have hstep := st249_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p145 : ((2477237595871/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT249 (i+1))
      = (∑ i ∈ Finset.range 144, stT249 (i+1)) + stT249 145 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 144
    simpa using h
  have hprev := st249_p144
  have hstep := st249_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p146 : ((4551544865567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT249 (i+1))
      = (∑ i ∈ Finset.range 145, stT249 (i+1)) + stT249 146 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 145
    simpa using h
  have hprev := st249_p145
  have hstep := st249_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p147 : ((1803959393273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT249 (i+1))
      = (∑ i ∈ Finset.range 146, stT249 (i+1)) + stT249 147 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 146
    simpa using h
  have hprev := st249_p146
  have hstep := st249_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p148 : ((9841641363457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT249 (i+1))
      = (∑ i ∈ Finset.range 147, stT249 (i+1)) + stT249 148 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 147
    simpa using h
  have hprev := st249_p147
  have hstep := st249_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p149 : ((9741711444097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT249 (i+1))
      = (∑ i ∈ Finset.range 148, stT249 (i+1)) + stT249 149 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 148
    simpa using h
  have hprev := st249_p148
  have hstep := st249_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p150 : ((4472159012203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT249 (i+1))
      = (∑ i ∈ Finset.range 149, stT249 (i+1)) + stT249 150 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 149
    simpa using h
  have hprev := st249_p149
  have hstep := st249_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p151 : ((4592649277271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT249 (i+1))
      = (∑ i ∈ Finset.range 150, stT249 (i+1)) + stT249 151 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 150
    simpa using h
  have hprev := st249_p150
  have hstep := st249_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p152 : ((4970227696841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT249 (i+1))
      = (∑ i ∈ Finset.range 151, stT249 (i+1)) + stT249 152 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 151
    simpa using h
  have hprev := st249_p151
  have hstep := st249_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p153 : ((9599389284307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT249 (i+1))
      = (∑ i ∈ Finset.range 152, stT249 (i+1)) + stT249 153 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 152
    simpa using h
  have hprev := st249_p152
  have hstep := st249_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p154 : ((1777428657201/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT249 (i+1))
      = (∑ i ∈ Finset.range 153, stT249 (i+1)) + stT249 154 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 153
    simpa using h
  have hprev := st249_p153
  have hstep := st249_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p155 : ((9291546381687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT249 (i+1))
      = (∑ i ∈ Finset.range 154, stT249 (i+1)) + stT249 155 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 154
    simpa using h
  have hprev := st249_p154
  have hstep := st249_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p156 : ((9970627612407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT249 (i+1))
      = (∑ i ∈ Finset.range 155, stT249 (i+1)) + stT249 156 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 155
    simpa using h
  have hprev := st249_p155
  have hstep := st249_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p157 : ((4767129988839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT249 (i+1))
      = (∑ i ∈ Finset.range 156, stT249 (i+1)) + stT249 157 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 156
    simpa using h
  have hprev := st249_p156
  have hstep := st249_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p158 : ((4436268554451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT249 (i+1))
      = (∑ i ∈ Finset.range 157, stT249 (i+1)) + stT249 158 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 157
    simpa using h
  have hprev := st249_p157
  have hstep := st249_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p159 : ((1862584141671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT249 (i+1))
      = (∑ i ∈ Finset.range 158, stT249 (i+1)) + stT249 159 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 158
    simpa using h
  have hprev := st249_p158
  have hstep := st249_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p160 : ((1246817796309/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT249 (i+1))
      = (∑ i ∈ Finset.range 159, stT249 (i+1)) + stT249 160 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 159
    simpa using h
  have hprev := st249_p159
  have hstep := st249_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p161 : ((9556056217583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT249 (i+1))
      = (∑ i ∈ Finset.range 160, stT249 (i+1)) + stT249 161 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 160
    simpa using h
  have hprev := st249_p160
  have hstep := st249_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p162 : ((4439210871929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT249 (i+1))
      = (∑ i ∈ Finset.range 161, stT249 (i+1)) + stT249 162 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 161
    simpa using h
  have hprev := st249_p161
  have hstep := st249_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p163 : ((4624281894509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT249 (i+1))
      = (∑ i ∈ Finset.range 162, stT249 (i+1)) + stT249 163 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 162
    simpa using h
  have hprev := st249_p162
  have hstep := st249_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p164 : ((4976773908823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT249 (i+1))
      = (∑ i ∈ Finset.range 163, stT249 (i+1)) + stT249 164 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 163
    simpa using h
  have hprev := st249_p163
  have hstep := st249_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p165 : ((9659500181857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT249 (i+1))
      = (∑ i ∈ Finset.range 164, stT249 (i+1)) + stT249 165 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 164
    simpa using h
  have hprev := st249_p164
  have hstep := st249_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p166 : ((4461478471769/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT249 (i+1))
      = (∑ i ∈ Finset.range 165, stT249 (i+1)) + stT249 166 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 165
    simpa using h
  have hprev := st249_p165
  have hstep := st249_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p167 : ((4555579991507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT249 (i+1))
      = (∑ i ∈ Finset.range 166, stT249 (i+1)) + stT249 167 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 166
    simpa using h
  have hprev := st249_p166
  have hstep := st249_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p168 : ((4936299606269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT249 (i+1))
      = (∑ i ∈ Finset.range 167, stT249 (i+1)) + stT249 168 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 167
    simpa using h
  have hprev := st249_p167
  have hstep := st249_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p169 : ((9819944581357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT249 (i+1))
      = (∑ i ∈ Finset.range 168, stT249 (i+1)) + stT249 169 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 168
    simpa using h
  have hprev := st249_p168
  have hstep := st249_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p170 : ((4526683449341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT249 (i+1))
      = (∑ i ∈ Finset.range 169, stT249 (i+1)) + stT249 170 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 169
    simpa using h
  have hprev := st249_p169
  have hstep := st249_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p171 : ((4471907320461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT249 (i+1))
      = (∑ i ∈ Finset.range 170, stT249 (i+1)) + stT249 171 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 170
    simpa using h
  have hprev := st249_p170
  have hstep := st249_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p172 : ((4840064001543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT249 (i+1))
      = (∑ i ∈ Finset.range 171, stT249 (i+1)) + stT249 172 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 171
    simpa using h
  have hprev := st249_p171
  have hstep := st249_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p173 : ((9969087242181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT249 (i+1))
      = (∑ i ∈ Finset.range 172, stT249 (i+1)) + stT249 173 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 172
    simpa using h
  have hprev := st249_p172
  have hstep := st249_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p174 : ((74506082767/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT249 (i+1))
      = (∑ i ∈ Finset.range 173, stT249 (i+1)) + stT249 174 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 173
    simpa using h
  have hprev := st249_p173
  have hstep := st249_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p175 : ((4422075609279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT249 (i+1))
      = (∑ i ∈ Finset.range 174, stT249 (i+1)) + stT249 175 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 174
    simpa using h
  have hprev := st249_p174
  have hstep := st249_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p176 : ((935758258059/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT249 (i+1))
      = (∑ i ∈ Finset.range 175, stT249 (i+1)) + stT249 176 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 175
    simpa using h
  have hprev := st249_p175
  have hstep := st249_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p177 : ((4991188897523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT249 (i+1))
      = (∑ i ∈ Finset.range 176, stT249 (i+1)) + stT249 177 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 176
    simpa using h
  have hprev := st249_p176
  have hstep := st249_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p178 : ((967575324823/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT249 (i+1))
      = (∑ i ∈ Finset.range 177, stT249 (i+1)) + stT249 178 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 177
    simpa using h
  have hprev := st249_p177
  have hstep := st249_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p179 : ((4475352599369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT249 (i+1))
      = (∑ i ∈ Finset.range 178, stT249 (i+1)) + stT249 179 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 178
    simpa using h
  have hprev := st249_p178
  have hstep := st249_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p180 : ((8996819567233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT249 (i+1))
      = (∑ i ∈ Finset.range 179, stT249 (i+1)) + stT249 180 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 179
    simpa using h
  have hprev := st249_p179
  have hstep := st249_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p181 : ((9733869154339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT249 (i+1))
      = (∑ i ∈ Finset.range 180, stT249 (i+1)) + stT249 181 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 180
    simpa using h
  have hprev := st249_p180
  have hstep := st249_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p182 : ((9972790014517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT249 (i+1))
      = (∑ i ∈ Finset.range 181, stT249 (i+1)) + stT249 182 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 181
    simpa using h
  have hprev := st249_p181
  have hstep := st249_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p183 : ((9336685787407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT249 (i+1))
      = (∑ i ∈ Finset.range 182, stT249 (i+1)) + stT249 183 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 182
    simpa using h
  have hprev := st249_p182
  have hstep := st249_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p184 : ((8834958354447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT249 (i+1))
      = (∑ i ∈ Finset.range 183, stT249 (i+1)) + stT249 184 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 183
    simpa using h
  have hprev := st249_p183
  have hstep := st249_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p185 : ((9250736575727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT249 (i+1))
      = (∑ i ∈ Finset.range 184, stT249 (i+1)) + stT249 185 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 184
    simpa using h
  have hprev := st249_p184
  have hstep := st249_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p186 : ((9933612995927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT249 (i+1))
      = (∑ i ∈ Finset.range 185, stT249 (i+1)) + stT249 186 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 185
    simpa using h
  have hprev := st249_p185
  have hstep := st249_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p187 : ((4916860186427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT249 (i+1))
      = (∑ i ∈ Finset.range 186, stT249 (i+1)) + stT249 187 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 186
    simpa using h
  have hprev := st249_p186
  have hstep := st249_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p188 : ((4554219375327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT249 (i+1))
      = (∑ i ∈ Finset.range 187, stT249 (i+1)) + stT249 188 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 187
    simpa using h
  have hprev := st249_p187
  have hstep := st249_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p189 : ((4427561341809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT249 (i+1))
      = (∑ i ∈ Finset.range 188, stT249 (i+1)) + stT249 189 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 188
    simpa using h
  have hprev := st249_p188
  have hstep := st249_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p190 : ((944869046087/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT249 (i+1))
      = (∑ i ∈ Finset.range 189, stT249 (i+1)) + stT249 190 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 189
    simpa using h
  have hprev := st249_p189
  have hstep := st249_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p191 : ((5002285922463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT249 (i+1))
      = (∑ i ∈ Finset.range 190, stT249 (i+1)) + stT249 191 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 190
    simpa using h
  have hprev := st249_p190
  have hstep := st249_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p192 : ((4853786347767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT249 (i+1))
      = (∑ i ∈ Finset.range 191, stT249 (i+1)) + stT249 192 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 191
    simpa using h
  have hprev := st249_p191
  have hstep := st249_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p193 : ((4497730802999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT249 (i+1))
      = (∑ i ∈ Finset.range 192, stT249 (i+1)) + stT249 193 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 192
    simpa using h
  have hprev := st249_p192
  have hstep := st249_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p194 : ((1112156140319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT249 (i+1))
      = (∑ i ∈ Finset.range 193, stT249 (i+1)) + stT249 194 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 193
    simpa using h
  have hprev := st249_p193
  have hstep := st249_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p195 : ((954880329711/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT249 (i+1))
      = (∑ i ∈ Finset.range 194, stT249 (i+1)) + stT249 195 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 194
    simpa using h
  have hprev := st249_p194
  have hstep := st249_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p196 : ((400895227227/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT249 (i+1))
      = (∑ i ∈ Finset.range 195, stT249 (i+1)) + stT249 196 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 195
    simpa using h
  have hprev := st249_p195
  have hstep := st249_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p197 : ((4827320455719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT249 (i+1))
      = (∑ i ∈ Finset.range 196, stT249 (i+1)) + stT249 197 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 196
    simpa using h
  have hprev := st249_p196
  have hstep := st249_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p198 : ((4481508433719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT249 (i+1))
      = (∑ i ∈ Finset.range 197, stT249 (i+1)) + stT249 198 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 197
    simpa using h
  have hprev := st249_p197
  have hstep := st249_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p199 : ((2225853339999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT249 (i+1))
      = (∑ i ∈ Finset.range 198, stT249 (i+1)) + stT249 199 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 198
    simpa using h
  have hprev := st249_p198
  have hstep := st249_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p200 : ((2388193563903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT249 (i+1))
      = (∑ i ∈ Finset.range 199, stT249 (i+1)) + stT249 200 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 199
    simpa using h
  have hprev := st249_p199
  have hstep := st249_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p201 : ((10026099544587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT249 (i+1))
      = (∑ i ∈ Finset.range 200, stT249 (i+1)) + stT249 201 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 200
    simpa using h
  have hprev := st249_p200
  have hstep := st249_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p202 : ((9688732746763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT249 (i+1))
      = (∑ i ∈ Finset.range 201, stT249 (i+1)) + stT249 202 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 201
    simpa using h
  have hprev := st249_p201
  have hstep := st249_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p203 : ((4497835905323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT249 (i+1))
      = (∑ i ∈ Finset.range 202, stT249 (i+1)) + stT249 203 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 202
    simpa using h
  have hprev := st249_p202
  have hstep := st249_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p204 : ((554033725137/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT249 (i+1))
      = (∑ i ∈ Finset.range 203, stT249 (i+1)) + stT249 204 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 203
    simpa using h
  have hprev := st249_p203
  have hstep := st249_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p205 : ((4731499912071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT249 (i+1))
      = (∑ i ∈ Finset.range 204, stT249 (i+1)) + stT249 205 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 204
    simpa using h
  have hprev := st249_p204
  have hstep := st249_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p206 : ((5004509164257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT249 (i+1))
      = (∑ i ∈ Finset.range 205, stT249 (i+1)) + stT249 206 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 205
    simpa using h
  have hprev := st249_p205
  have hstep := st249_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p207 : ((9800163749553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT249 (i+1))
      = (∑ i ∈ Finset.range 206, stT249 (i+1)) + stT249 207 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 206
    simpa using h
  have hprev := st249_p206
  have hstep := st249_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p208 : ((9108245919281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT249 (i+1))
      = (∑ i ∈ Finset.range 207, stT249 (i+1)) + stT249 208 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 207
    simpa using h
  have hprev := st249_p207
  have hstep := st249_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p209 : ((4406109438083/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT249 (i+1))
      = (∑ i ∈ Finset.range 208, stT249 (i+1)) + stT249 209 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 208
    simpa using h
  have hprev := st249_p208
  have hstep := st249_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p210 : ((9280724016551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT249 (i+1))
      = (∑ i ∈ Finset.range 209, stT249 (i+1)) + stT249 210 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 209
    simpa using h
  have hprev := st249_p209
  have hstep := st249_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p211 : ((397014251699/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT249 (i+1))
      = (∑ i ∈ Finset.range 210, stT249 (i+1)) + stT249 211 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 210
    simpa using h
  have hprev := st249_p210
  have hstep := st249_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p212 : ((9949372384811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT249 (i+1))
      = (∑ i ∈ Finset.range 211, stT249 (i+1)) + stT249 212 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 211
    simpa using h
  have hprev := st249_p211
  have hstep := st249_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p213 : ((233192184663/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT249 (i+1))
      = (∑ i ∈ Finset.range 212, stT249 (i+1)) + stT249 213 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 212
    simpa using h
  have hprev := st249_p212
  have hstep := st249_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p214 : ((440964198537/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT249 (i+1))
      = (∑ i ∈ Finset.range 213, stT249 (i+1)) + stT249 214 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 213
    simpa using h
  have hprev := st249_p213
  have hstep := st249_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p215 : ((451762891533/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT249 (i+1))
      = (∑ i ∈ Finset.range 214, stT249 (i+1)) + stT249 215 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 214
    simpa using h
  have hprev := st249_p214
  have hstep := st249_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p216 : ((9712692662959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT249 (i+1))
      = (∑ i ∈ Finset.range 215, stT249 (i+1)) + stT249 216 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 215
    simpa using h
  have hprev := st249_p215
  have hstep := st249_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p217 : ((2009254506299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT249 (i+1))
      = (∑ i ∈ Finset.range 216, stT249 (i+1)) + stT249 217 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 216
    simpa using h
  have hprev := st249_p216
  have hstep := st249_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p218 : ((9646627736047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT249 (i+1))
      = (∑ i ∈ Finset.range 217, stT249 (i+1)) + stT249 218 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 217
    simpa using h
  have hprev := st249_p217
  have hstep := st249_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p219 : ((8984309892727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT249 (i+1))
      = (∑ i ∈ Finset.range 218, stT249 (i+1)) + stT249 219 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 218
    simpa using h
  have hprev := st249_p218
  have hstep := st249_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p220 : ((8826297638727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT249 (i+1))
      = (∑ i ∈ Finset.range 219, stT249 (i+1)) + stT249 220 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 219
    simpa using h
  have hprev := st249_p219
  have hstep := st249_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p221 : ((9350138940711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT249 (i+1))
      = (∑ i ∈ Finset.range 220, stT249 (i+1)) + stT249 221 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 220
    simpa using h
  have hprev := st249_p220
  have hstep := st249_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p222 : ((9955584070219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT249 (i+1))
      = (∑ i ∈ Finset.range 221, stT249 (i+1)) + stT249 222 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 221
    simpa using h
  have hprev := st249_p221
  have hstep := st249_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p223 : ((9959304640063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT249 (i+1))
      = (∑ i ∈ Finset.range 222, stT249 (i+1)) + stT249 223 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 222
    simpa using h
  have hprev := st249_p222
  have hstep := st249_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p224 : ((9361254694051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT249 (i+1))
      = (∑ i ∈ Finset.range 223, stT249 (i+1)) + stT249 224 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 223
    simpa using h
  have hprev := st249_p223
  have hstep := st249_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p225 : ((8829227761371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT249 (i+1))
      = (∑ i ∈ Finset.range 224, stT249 (i+1)) + stT249 225 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 224
    simpa using h
  have hprev := st249_p224
  have hstep := st249_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p226 : ((8948447104311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT249 (i+1))
      = (∑ i ∈ Finset.range 225, stT249 (i+1)) + stT249 226 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 225
    simpa using h
  have hprev := st249_p225
  have hstep := st249_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p227 : ((149753044431/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT249 (i+1))
      = (∑ i ∈ Finset.range 226, stT249 (i+1)) + stT249 227 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 226
    simpa using h
  have hprev := st249_p226
  have hstep := st249_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p228 : ((1004399354433/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT249 (i+1))
      = (∑ i ∈ Finset.range 227, stT249 (i+1)) + stT249 228 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 227
    simpa using h
  have hprev := st249_p227
  have hstep := st249_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p229 : ((4917344188773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT249 (i+1))
      = (∑ i ∈ Finset.range 228, stT249 (i+1)) + stT249 229 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 228
    simpa using h
  have hprev := st249_p228
  have hstep := st249_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p230 : ((1148009807951/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT249 (i+1))
      = (∑ i ∈ Finset.range 229, stT249 (i+1)) + stT249 230 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 229
    simpa using h
  have hprev := st249_p229
  have hstep := st249_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p231 : ((219592554263/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT249 (i+1))
      = (∑ i ∈ Finset.range 230, stT249 (i+1)) + stT249 231 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 230
    simpa using h
  have hprev := st249_p230
  have hstep := st249_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p232 : ((282882690019/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT249 (i+1))
      = (∑ i ∈ Finset.range 231, stT249 (i+1)) + stT249 232 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 231
    simpa using h
  have hprev := st249_p231
  have hstep := st249_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p233 : ((606582693943/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT249 (i+1))
      = (∑ i ∈ Finset.range 232, stT249 (i+1)) + stT249 233 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 232
    simpa using h
  have hprev := st249_p232
  have hstep := st249_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p234 : ((78633291381/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT249 (i+1))
      = (∑ i ∈ Finset.range 233, stT249 (i+1)) + stT249 234 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 233
    simpa using h
  have hprev := st249_p233
  have hstep := st249_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p235 : ((9764340889413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT249 (i+1))
      = (∑ i ∈ Finset.range 234, stT249 (i+1)) + stT249 235 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 234
    simpa using h
  have hprev := st249_p234
  have hstep := st249_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p236 : ((9113748701603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT249 (i+1))
      = (∑ i ∈ Finset.range 235, stT249 (i+1)) + stT249 236 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 235
    simpa using h
  have hprev := st249_p235
  have hstep := st249_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p237 : ((8772889442383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT249 (i+1))
      = (∑ i ∈ Finset.range 236, stT249 (i+1)) + stT249 237 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 236
    simpa using h
  have hprev := st249_p236
  have hstep := st249_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p238 : ((2270344095079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT249 (i+1))
      = (∑ i ∈ Finset.range 237, stT249 (i+1)) + stT249 238 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 237
    simpa using h
  have hprev := st249_p237
  have hstep := st249_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p239 : ((194557707471/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT249 (i+1))
      = (∑ i ∈ Finset.range 238, stT249 (i+1)) + stT249 239 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 238
    simpa using h
  have hprev := st249_p238
  have hstep := st249_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p240 : ((2014346388599/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT249 (i+1))
      = (∑ i ∈ Finset.range 239, stT249 (i+1)) + stT249 240 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 239
    simpa using h
  have hprev := st249_p239
  have hstep := st249_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p241 : ((977795448079/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT249 (i+1))
      = (∑ i ∈ Finset.range 240, stT249 (i+1)) + stT249 241 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 240
    simpa using h
  have hprev := st249_p240
  have hstep := st249_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p242 : ((456825320597/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT249 (i+1))
      = (∑ i ∈ Finset.range 241, stT249 (i+1)) + stT249 242 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 241
    simpa using h
  have hprev := st249_p241
  have hstep := st249_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p243 : ((4384431735921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT249 (i+1))
      = (∑ i ∈ Finset.range 242, stT249 (i+1)) + stT249 243 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 242
    simpa using h
  have hprev := st249_p242
  have hstep := st249_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p244 : ((4512703803541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT249 (i+1))
      = (∑ i ∈ Finset.range 243, stT249 (i+1)) + stT249 244 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 243
    simpa using h
  have hprev := st249_p243
  have hstep := st249_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p245 : ((4828999172497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT249 (i+1))
      = (∑ i ∈ Finset.range 244, stT249 (i+1)) + stT249 245 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 244
    simpa using h
  have hprev := st249_p244
  have hstep := st249_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p246 : ((201340462277/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT249 (i+1))
      = (∑ i ∈ Finset.range 245, stT249 (i+1)) + stT249 246 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 245
    simpa using h
  have hprev := st249_p245
  have hstep := st249_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p247 : ((1974143165873/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT249 (i+1))
      = (∑ i ∈ Finset.range 246, stT249 (i+1)) + stT249 247 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 246
    simpa using h
  have hprev := st249_p246
  have hstep := st249_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p248 : ((1156950620711/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT249 (i+1))
      = (∑ i ∈ Finset.range 247, stT249 (i+1)) + stT249 248 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 247
    simpa using h
  have hprev := st249_p247
  have hstep := st249_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p249 : ((8792251228413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT249 (i+1))
      = (∑ i ∈ Finset.range 248, stT249 (i+1)) + stT249 249 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 248
    simpa using h
  have hprev := st249_p248
  have hstep := st249_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p250 : ((2226061748067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT249 (i+1))
      = (∑ i ∈ Finset.range 249, stT249 (i+1)) + stT249 250 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 249
    simpa using h
  have hprev := st249_p249
  have hstep := st249_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p251 : ((1185737321901/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT249 (i+1))
      = (∑ i ∈ Finset.range 250, stT249 (i+1)) + stT249 251 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 250
    simpa using h
  have hprev := st249_p250
  have hstep := st249_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p252 : ((2502210659067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT249 (i+1))
      = (∑ i ∈ Finset.range 251, stT249 (i+1)) + stT249 252 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 251
    simpa using h
  have hprev := st249_p251
  have hstep := st249_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p253 : ((625288455693/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT249 (i+1))
      = (∑ i ∈ Finset.range 252, stT249 (i+1)) + stT249 253 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 252
    simpa using h
  have hprev := st249_p252
  have hstep := st249_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p254 : ((118504791657/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT249 (i+1))
      = (∑ i ∈ Finset.range 253, stT249 (i+1)) + stT249 254 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 253
    simpa using h
  have hprev := st249_p253
  have hstep := st249_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p255 : ((1780543539547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT249 (i+1))
      = (∑ i ∈ Finset.range 254, stT249 (i+1)) + stT249 255 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 254
    simpa using h
  have hprev := st249_p254
  have hstep := st249_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p256 : ((548668632769/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT249 (i+1))
      = (∑ i ∈ Finset.range 255, stT249 (i+1)) + stT249 256 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 255
    simpa using h
  have hprev := st249_p255
  have hstep := st249_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p257 : ((4606685627137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT249 (i+1))
      = (∑ i ∈ Finset.range 256, stT249 (i+1)) + stT249 257 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 256
    simpa using h
  have hprev := st249_p256
  have hstep := st249_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p258 : ((982722600113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT249 (i+1))
      = (∑ i ∈ Finset.range 257, stT249 (i+1)) + stT249 258 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 257
    simpa using h
  have hprev := st249_p257
  have hstep := st249_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p259 : ((1009202861417/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT249 (i+1))
      = (∑ i ∈ Finset.range 258, stT249 (i+1)) + stT249 259 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 258
    simpa using h
  have hprev := st249_p258
  have hstep := st249_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p260 : ((4892125571073/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT249 (i+1))
      = (∑ i ∈ Finset.range 259, stT249 (i+1)) + stT249 260 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 259
    simpa using h
  have hprev := st249_p259
  have hstep := st249_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p261 : ((9168067049271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT249 (i+1))
      = (∑ i ∈ Finset.range 260, stT249 (i+1)) + stT249 261 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 260
    simpa using h
  have hprev := st249_p260
  have hstep := st249_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p262 : ((8763328241093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT249 (i+1))
      = (∑ i ∈ Finset.range 261, stT249 (i+1)) + stT249 262 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 261
    simpa using h
  have hprev := st249_p261
  have hstep := st249_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p263 : ((8906444052563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT249 (i+1))
      = (∑ i ∈ Finset.range 262, stT249 (i+1)) + stT249 263 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 262
    simpa using h
  have hprev := st249_p262
  have hstep := st249_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p264 : ((4737647785619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT249 (i+1))
      = (∑ i ∈ Finset.range 263, stT249 (i+1)) + stT249 264 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 263
    simpa using h
  have hprev := st249_p263
  have hstep := st249_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p265 : ((4999505772449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT249 (i+1))
      = (∑ i ∈ Finset.range 264, stT249 (i+1)) + stT249 265 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 264
    simpa using h
  have hprev := st249_p264
  have hstep := st249_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p266 : ((5024930194223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT249 (i+1))
      = (∑ i ∈ Finset.range 265, stT249 (i+1)) + stT249 266 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 265
    simpa using h
  have hprev := st249_p265
  have hstep := st249_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p267 : ((1917910149161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT249 (i+1))
      = (∑ i ∈ Finset.range 266, stT249 (i+1)) + stT249 267 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 266
    simpa using h
  have hprev := st249_p266
  have hstep := st249_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p268 : ((8992256241229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT249 (i+1))
      = (∑ i ∈ Finset.range 267, stT249 (i+1)) + stT249 268 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 267
    simpa using h
  have hprev := st249_p267
  have hstep := st249_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p269 : ((4368436041029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT249 (i+1))
      = (∑ i ∈ Finset.range 268, stT249 (i+1)) + stT249 269 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 268
    simpa using h
  have hprev := st249_p268
  have hstep := st249_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p270 : ((4512111433169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT249 (i+1))
      = (∑ i ∈ Finset.range 269, stT249 (i+1)) + stT249 270 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 269
    simpa using h
  have hprev := st249_p269
  have hstep := st249_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p271 : ((4812018838657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT249 (i+1))
      = (∑ i ∈ Finset.range 270, stT249 (i+1)) + stT249 271 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 270
    simpa using h
  have hprev := st249_p270
  have hstep := st249_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p272 : ((251601659459/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT249 (i+1))
      = (∑ i ∈ Finset.range 271, stT249 (i+1)) + stT249 272 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 271
    simpa using h
  have hprev := st249_p271
  have hstep := st249_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p273 : ((2500660901081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT249 (i+1))
      = (∑ i ∈ Finset.range 272, stT249 (i+1)) + stT249 273 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 272
    simpa using h
  have hprev := st249_p272
  have hstep := st249_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p274 : ((1898072722329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT249 (i+1))
      = (∑ i ∈ Finset.range 273, stT249 (i+1)) + stT249 274 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 273
    simpa using h
  have hprev := st249_p273
  have hstep := st249_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p275 : ((2855528967/3200000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT249 (i+1))
      = (∑ i ∈ Finset.range 274, stT249 (i+1)) + stT249 275 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 274
    simpa using h
  have hprev := st249_p274
  have hstep := st249_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p276 : ((1746986142469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT249 (i+1))
      = (∑ i ∈ Finset.range 275, stT249 (i+1)) + stT249 276 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 275
    simpa using h
  have hprev := st249_p275
  have hstep := st249_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p277 : ((4532570754983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT249 (i+1))
      = (∑ i ∈ Finset.range 276, stT249 (i+1)) + stT249 277 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 276
    simpa using h
  have hprev := st249_p276
  have hstep := st249_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p278 : ((4831179263783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT249 (i+1))
      = (∑ i ∈ Finset.range 277, stT249 (i+1)) + stT249 278 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 277
    simpa using h
  have hprev := st249_p277
  have hstep := st249_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p279 : ((5039184236691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT249 (i+1))
      = (∑ i ∈ Finset.range 278, stT249 (i+1)) + stT249 279 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 278
    simpa using h
  have hprev := st249_p278
  have hstep := st249_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p280 : ((2501316155223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT249 (i+1))
      = (∑ i ∈ Finset.range 279, stT249 (i+1)) + stT249 280 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 279
    simpa using h
  have hprev := st249_p279
  have hstep := st249_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p281 : ((2374993113423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT249 (i+1))
      = (∑ i ∈ Finset.range 280, stT249 (i+1)) + stT249 281 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 280
    simpa using h
  have hprev := st249_p280
  have hstep := st249_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p282 : ((1116929787037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT249 (i+1))
      = (∑ i ∈ Finset.range 281, stT249 (i+1)) + stT249 282 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 281
    simpa using h
  have hprev := st249_p281
  have hstep := st249_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p283 : ((4361510137579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT249 (i+1))
      = (∑ i ∈ Finset.range 282, stT249 (i+1)) + stT249 283 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 282
    simpa using h
  have hprev := st249_p282
  have hstep := st249_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p284 : ((2253549928777/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT249 (i+1))
      = (∑ i ∈ Finset.range 283, stT249 (i+1)) + stT249 284 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 283
    simpa using h
  have hprev := st249_p283
  have hstep := st249_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p285 : ((239916668953/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT249 (i+1))
      = (∑ i ∈ Finset.range 284, stT249 (i+1)) + stT249 285 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 284
    simpa using h
  have hprev := st249_p284
  have hstep := st249_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p286 : ((1256607034883/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT249 (i+1))
      = (∑ i ∈ Finset.range 285, stT249 (i+1)) + stT249 286 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 285
    simpa using h
  have hprev := st249_p285
  have hstep := st249_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p287 : ((5029997568739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT249 (i+1))
      = (∑ i ∈ Finset.range 286, stT249 (i+1)) + stT249 287 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 286
    simpa using h
  have hprev := st249_p286
  have hstep := st249_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p288 : ((4807872805491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT249 (i+1))
      = (∑ i ∈ Finset.range 287, stT249 (i+1)) + stT249 288 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 287
    simpa using h
  have hprev := st249_p287
  have hstep := st249_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p289 : ((4516878338651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT249 (i+1))
      = (∑ i ∈ Finset.range 288, stT249 (i+1)) + stT249 289 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 288
    simpa using h
  have hprev := st249_p288
  have hstep := st249_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p290 : ((8719586982871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT249 (i+1))
      = (∑ i ∈ Finset.range 289, stT249 (i+1)) + stT249 290 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 289
    simpa using h
  have hprev := st249_p289
  have hstep := st249_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p291 : ((8888685705681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT249 (i+1))
      = (∑ i ∈ Finset.range 290, stT249 (i+1)) + stT249 291 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 290
    simpa using h
  have hprev := st249_p290
  have hstep := st249_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p292 : ((2355516091419/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT249 (i+1))
      = (∑ i ∈ Finset.range 291, stT249 (i+1)) + stT249 292 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 291
    simpa using h
  have hprev := st249_p291
  have hstep := st249_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p293 : ((4976847957559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT249 (i+1))
      = (∑ i ∈ Finset.range 292, stT249 (i+1)) + stT249 293 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 292
    simpa using h
  have hprev := st249_p292
  have hstep := st249_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p294 : ((5061629340629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT249 (i+1))
      = (∑ i ∈ Finset.range 293, stT249 (i+1)) + stT249 294 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 293
    simpa using h
  have hprev := st249_p293
  have hstep := st249_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p295 : ((2454671255263/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT249 (i+1))
      = (∑ i ∈ Finset.range 294, stT249 (i+1)) + stT249 295 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 294
    simpa using h
  have hprev := st249_p294
  have hstep := st249_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p296 : ((4623285155437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT249 (i+1))
      = (∑ i ∈ Finset.range 295, stT249 (i+1)) + stT249 296 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 295
    simpa using h
  have hprev := st249_p295
  have hstep := st249_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p297 : ((2197222175897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT249 (i+1))
      = (∑ i ∈ Finset.range 296, stT249 (i+1)) + stT249 297 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 296
    simpa using h
  have hprev := st249_p296
  have hstep := st249_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p298 : ((8747340645533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT249 (i+1))
      = (∑ i ∈ Finset.range 297, stT249 (i+1)) + stT249 298 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 297
    simpa using h
  have hprev := st249_p297
  have hstep := st249_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p299 : ((9146746848179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT249 (i+1))
      = (∑ i ∈ Finset.range 298, stT249 (i+1)) + stT249 299 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 298
    simpa using h
  have hprev := st249_p298
  have hstep := st249_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p300 : ((9723914982929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT249 (i+1))
      = (∑ i ∈ Finset.range 299, stT249 (i+1)) + stT249 300 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 299
    simpa using h
  have hprev := st249_p299
  have hstep := st249_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p301 : ((10103577888419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT249 (i+1))
      = (∑ i ∈ Finset.range 300, stT249 (i+1)) + stT249 301 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 300
    simpa using h
  have hprev := st249_p300
  have hstep := st249_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p302 : ((10042243891487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT249 (i+1))
      = (∑ i ∈ Finset.range 301, stT249 (i+1)) + stT249 302 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 301
    simpa using h
  have hprev := st249_p301
  have hstep := st249_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p303 : ((4790868070501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT249 (i+1))
      = (∑ i ∈ Finset.range 302, stT249 (i+1)) + stT249 303 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 302
    simpa using h
  have hprev := st249_p302
  have hstep := st249_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p304 : ((4508692125901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT249 (i+1))
      = (∑ i ∈ Finset.range 303, stT249 (i+1)) + stT249 304 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 303
    simpa using h
  have hprev := st249_p303
  have hstep := st249_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p305 : ((54416546073/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT249 (i+1))
      = (∑ i ∈ Finset.range 304, stT249 (i+1)) + stT249 305 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 304
    simpa using h
  have hprev := st249_p304
  have hstep := st249_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p306 : ((8843344664983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT249 (i+1))
      = (∑ i ∈ Finset.range 305, stT249 (i+1)) + stT249 306 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 305
    simpa using h
  have hprev := st249_p305
  have hstep := st249_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p307 : ((9339484819823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT249 (i+1))
      = (∑ i ∈ Finset.range 306, stT249 (i+1)) + stT249 307 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 306
    simpa using h
  have hprev := st249_p306
  have hstep := st249_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p308 : ((9884998439771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT249 (i+1))
      = (∑ i ∈ Finset.range 307, stT249 (i+1)) + stT249 308 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 307
    simpa using h
  have hprev := st249_p307
  have hstep := st249_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p309 : ((10143018514811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT249 (i+1))
      = (∑ i ∈ Finset.range 308, stT249 (i+1)) + stT249 309 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 308
    simpa using h
  have hprev := st249_p308
  have hstep := st249_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p310 : ((9956954163611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT249 (i+1))
      = (∑ i ∈ Finset.range 309, stT249 (i+1)) + stT249 310 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 309
    simpa using h
  have hprev := st249_p309
  have hstep := st249_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p311 : ((9442718746139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT249 (i+1))
      = (∑ i ∈ Finset.range 310, stT249 (i+1)) + stT249 311 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 310
    simpa using h
  have hprev := st249_p310
  have hstep := st249_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p312 : ((1114210774327/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT249 (i+1))
      = (∑ i ∈ Finset.range 311, stT249 (i+1)) + stT249 312 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 311
    simpa using h
  have hprev := st249_p311
  have hstep := st249_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p313 : ((2172114915893/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT249 (i+1))
      = (∑ i ∈ Finset.range 312, stT249 (i+1)) + stT249 313 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 312
    simpa using h
  have hprev := st249_p312
  have hstep := st249_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p314 : ((222502372147/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT249 (i+1))
      = (∑ i ∈ Finset.range 313, stT249 (i+1)) + stT249 314 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 313
    simpa using h
  have hprev := st249_p313
  have hstep := st249_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p315 : ((1177525895621/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT249 (i+1))
      = (∑ i ∈ Finset.range 314, stT249 (i+1)) + stT249 315 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 314
    simpa using h
  have hprev := st249_p314
  have hstep := st249_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p316 : ((9939479919951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT249 (i+1))
      = (∑ i ∈ Finset.range 315, stT249 (i+1)) + stT249 316 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 315
    simpa using h
  have hprev := st249_p315
  have hstep := st249_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p317 : ((10152690897811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT249 (i+1))
      = (∑ i ∈ Finset.range 316, stT249 (i+1)) + stT249 317 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 316
    simpa using h
  have hprev := st249_p316
  have hstep := st249_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p318 : ((1987393202179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT249 (i+1))
      = (∑ i ∈ Finset.range 317, stT249 (i+1)) + stT249 318 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 317
    simpa using h
  have hprev := st249_p317
  have hstep := st249_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p319 : ((2354994822791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT249 (i+1))
      = (∑ i ∈ Finset.range 318, stT249 (i+1)) + stT249 319 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 318
    simpa using h
  have hprev := st249_p318
  have hstep := st249_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p320 : ((8901887366717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT249 (i+1))
      = (∑ i ∈ Finset.range 319, stT249 (i+1)) + stT249 320 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 319
    simpa using h
  have hprev := st249_p319
  have hstep := st249_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p321 : ((8680036610929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT249 (i+1))
      = (∑ i ∈ Finset.range 320, stT249 (i+1)) + stT249 321 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 320
    simpa using h
  have hprev := st249_p320
  have hstep := st249_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p322 : ((8879333155679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT249 (i+1))
      = (∑ i ∈ Finset.range 321, stT249 (i+1)) + stT249 322 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 321
    simpa using h
  have hprev := st249_p321
  have hstep := st249_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p323 : ((9384387361409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT249 (i+1))
      = (∑ i ∈ Finset.range 322, stT249 (i+1)) + stT249 323 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 322
    simpa using h
  have hprev := st249_p322
  have hstep := st249_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p324 : ((4954352029657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT249 (i+1))
      = (∑ i ∈ Finset.range 323, stT249 (i+1)) + stT249 324 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 323
    simpa using h
  have hprev := st249_p323
  have hstep := st249_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p325 : ((5079126802357/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT249 (i+1))
      = (∑ i ∈ Finset.range 324, stT249 (i+1)) + stT249 325 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 324
    simpa using h
  have hprev := st249_p324
  have hstep := st249_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p326 : ((9995457998899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT249 (i+1))
      = (∑ i ∈ Finset.range 325, stT249 (i+1)) + stT249 326 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 325
    simpa using h
  have hprev := st249_p325
  have hstep := st249_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p327 : ((9512765779183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT249 (i+1))
      = (∑ i ∈ Finset.range 326, stT249 (i+1)) + stT249 327 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 326
    simpa using h
  have hprev := st249_p326
  have hstep := st249_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p328 : ((359112277949/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT249 (i+1))
      = (∑ i ∈ Finset.range 327, stT249 (i+1)) + stT249 328 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 327
    simpa using h
  have hprev := st249_p327
  have hstep := st249_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p329 : ((8683823241041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT249 (i+1))
      = (∑ i ∈ Finset.range 328, stT249 (i+1)) + stT249 329 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 328
    simpa using h
  have hprev := st249_p328
  have hstep := st249_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p330 : ((1757911265727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT249 (i+1))
      = (∑ i ∈ Finset.range 329, stT249 (i+1)) + stT249 330 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 329
    simpa using h
  have hprev := st249_p329
  have hstep := st249_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p331 : ((9235572307579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT249 (i+1))
      = (∑ i ∈ Finset.range 330, stT249 (i+1)) + stT249 331 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 330
    simpa using h
  have hprev := st249_p330
  have hstep := st249_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p332 : ((9779941271627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT249 (i+1))
      = (∑ i ∈ Finset.range 331, stT249 (i+1)) + stT249 332 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 331
    simpa using h
  have hprev := st249_p331
  have hstep := st249_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p333 : ((2026157278939/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT249 (i+1))
      = (∑ i ∈ Finset.range 332, stT249 (i+1)) + stT249 333 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 332
    simpa using h
  have hprev := st249_p332
  have hstep := st249_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p334 : ((10102449791183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT249 (i+1))
      = (∑ i ∈ Finset.range 333, stT249 (i+1)) + stT249 334 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 333
    simpa using h
  have hprev := st249_p333
  have hstep := st249_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p335 : ((2427987246009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT249 (i+1))
      = (∑ i ∈ Finset.range 334, stT249 (i+1)) + stT249 335 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 334
    simpa using h
  have hprev := st249_p334
  have hstep := st249_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p336 : ((9166664209001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT249 (i+1))
      = (∑ i ∈ Finset.range 335, stT249 (i+1)) + stT249 336 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 335
    simpa using h
  have hprev := st249_p335
  have hstep := st249_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p337 : ((4376325995313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT249 (i+1))
      = (∑ i ∈ Finset.range 336, stT249 (i+1)) + stT249 337 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 336
    simpa using h
  have hprev := st249_p336
  have hstep := st249_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p338 : ((27139167457/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT249 (i+1))
      = (∑ i ∈ Finset.range 337, stT249 (i+1)) + stT249 338 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 337
    simpa using h
  have hprev := st249_p337
  have hstep := st249_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p339 : ((899569315749/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT249 (i+1))
      = (∑ i ∈ Finset.range 338, stT249 (i+1)) + stT249 339 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 338
    simpa using h
  have hprev := st249_p338
  have hstep := st249_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p340 : ((4762023877539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT249 (i+1))
      = (∑ i ∈ Finset.range 339, stT249 (i+1)) + stT249 340 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 339
    simpa using h
  have hprev := st249_p339
  have hstep := st249_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p341 : ((4999107336129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT249 (i+1))
      = (∑ i ∈ Finset.range 340, stT249 (i+1)) + stT249 341 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 340
    simpa using h
  have hprev := st249_p340
  have hstep := st249_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p342 : ((5088657874833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT249 (i+1))
      = (∑ i ∈ Finset.range 341, stT249 (i+1)) + stT249 342 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 341
    simpa using h
  have hprev := st249_p341
  have hstep := st249_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p343 : ((4986162945983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT249 (i+1))
      = (∑ i ∈ Finset.range 342, stT249 (i+1)) + stT249 343 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 342
    simpa using h
  have hprev := st249_p342
  have hstep := st249_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p344 : ((4744178055323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT249 (i+1))
      = (∑ i ∈ Finset.range 343, stT249 (i+1)) + stT249 344 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 343
    simpa using h
  have hprev := st249_p343
  have hstep := st249_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p345 : ((2242229270329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT249 (i+1))
      = (∑ i ∈ Finset.range 344, stT249 (i+1)) + stT249 345 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 344
    simpa using h
  have hprev := st249_p344
  have hstep := st249_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p346 : ((86725338457/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT249 (i+1))
      = (∑ i ∈ Finset.range 345, stT249 (i+1)) + stT249 346 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 345
    simpa using h
  have hprev := st249_p345
  have hstep := st249_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p347 : ((1093078126831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT249 (i+1))
      = (∑ i ∈ Finset.range 346, stT249 (i+1)) + stT249 347 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 346
    simpa using h
  have hprev := st249_p346
  have hstep := st249_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p348 : ((571736543213/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT249 (i+1))
      = (∑ i ∈ Finset.range 347, stT249 (i+1)) + stT249 348 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 347
    simpa using h
  have hprev := st249_p347
  have hstep := st249_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p349 : ((4841519251807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT249 (i+1))
      = (∑ i ∈ Finset.range 348, stT249 (i+1)) + stT249 349 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 348
    simpa using h
  have hprev := st249_p348
  have hstep := st249_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p350 : ((5044631197543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT249 (i+1))
      = (∑ i ∈ Finset.range 349, stT249 (i+1)) + stT249 350 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 349
    simpa using h
  have hprev := st249_p349
  have hstep := st249_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p351 : ((5085273285223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT249 (i+1))
      = (∑ i ∈ Finset.range 350, stT249 (i+1)) + stT249 351 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 350
    simpa using h
  have hprev := st249_p350
  have hstep := st249_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p352 : ((1236181830087/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT249 (i+1))
      = (∑ i ∈ Finset.range 351, stT249 (i+1)) + stT249 352 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 351
    simpa using h
  have hprev := st249_p351
  have hstep := st249_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p353 : ((2345595730949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT249 (i+1))
      = (∑ i ∈ Finset.range 352, stT249 (i+1)) + stT249 353 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 352
    simpa using h
  have hprev := st249_p352
  have hstep := st249_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p354 : ((4445938940593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT249 (i+1))
      = (∑ i ∈ Finset.range 353, stT249 (i+1)) + stT249 354 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 353
    simpa using h
  have hprev := st249_p353
  have hstep := st249_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p355 : ((4325037352573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT249 (i+1))
      = (∑ i ∈ Finset.range 354, stT249 (i+1)) + stT249 355 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 354
    simpa using h
  have hprev := st249_p354
  have hstep := st249_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p356 : ((4384781377123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT249 (i+1))
      = (∑ i ∈ Finset.range 355, stT249 (i+1)) + stT249 356 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 355
    simpa using h
  have hprev := st249_p355
  have hstep := st249_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p357 : ((4596249052087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT249 (i+1))
      = (∑ i ∈ Finset.range 356, stT249 (i+1)) + stT249 357 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 356
    simpa using h
  have hprev := st249_p356
  have hstep := st249_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p358 : ((4860142111789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT249 (i+1))
      = (∑ i ∈ Finset.range 357, stT249 (i+1)) + stT249 358 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 357
    simpa using h
  have hprev := st249_p357
  have hstep := st249_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p359 : ((10107803315433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT249 (i+1))
      = (∑ i ∈ Finset.range 358, stT249 (i+1)) + stT249 359 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 358
    simpa using h
  have hprev := st249_p358
  have hstep := st249_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p360 : ((10177136743779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT249 (i+1))
      = (∑ i ∈ Finset.range 359, stT249 (i+1)) + stT249 360 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 359
    simpa using h
  have hprev := st249_p359
  have hstep := st249_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p361 : ((9898111369011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT249 (i+1))
      = (∑ i ∈ Finset.range 360, stT249 (i+1)) + stT249 361 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 360
    simpa using h
  have hprev := st249_p360
  have hstep := st249_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p362 : ((2349930268543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT249 (i+1))
      = (∑ i ∈ Finset.range 361, stT249 (i+1)) + stT249 362 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 361
    simpa using h
  have hprev := st249_p361
  have hstep := st249_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p363 : ((2227287265903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT249 (i+1))
      = (∑ i ∈ Finset.range 362, stT249 (i+1)) + stT249 363 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 362
    simpa using h
  have hprev := st249_p362
  have hstep := st249_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p364 : ((4323848550319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT249 (i+1))
      = (∑ i ∈ Finset.range 363, stT249 (i+1)) + stT249 364 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 363
    simpa using h
  have hprev := st249_p363
  have hstep := st249_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p365 : ((8731555222891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT249 (i+1))
      = (∑ i ∈ Finset.range 364, stT249 (i+1)) + stT249 365 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 364
    simpa using h
  have hprev := st249_p364
  have hstep := st249_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p366 : ((9121533025867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT249 (i+1))
      = (∑ i ∈ Finset.range 365, stT249 (i+1)) + stT249 366 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 365
    simpa using h
  have hprev := st249_p365
  have hstep := st249_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p367 : ((4821435417081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT249 (i+1))
      = (∑ i ∈ Finset.range 366, stT249 (i+1)) + stT249 367 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 366
    simpa using h
  have hprev := st249_p366
  have hstep := st249_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p368 : ((2516139331143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT249 (i+1))
      = (∑ i ∈ Finset.range 367, stT249 (i+1)) + stT249 368 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 367
    simpa using h
  have hprev := st249_p367
  have hstep := st249_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p369 : ((10201735617441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT249 (i+1))
      = (∑ i ∈ Finset.range 368, stT249 (i+1)) + stT249 369 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 368
    simpa using h
  have hprev := st249_p368
  have hstep := st249_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p370 : ((9995826770493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT249 (i+1))
      = (∑ i ∈ Finset.range 369, stT249 (i+1)) + stT249 370 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 369
    simpa using h
  have hprev := st249_p369
  have hstep := st249_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p371 : ((9538098208443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT249 (i+1))
      = (∑ i ∈ Finset.range 370, stT249 (i+1)) + stT249 371 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 370
    simpa using h
  have hprev := st249_p370
  have hstep := st249_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p372 : ((9027851977991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT249 (i+1))
      = (∑ i ∈ Finset.range 371, stT249 (i+1)) + stT249 372 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 371
    simpa using h
  have hprev := st249_p371
  have hstep := st249_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p373 : ((4342497761063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT249 (i+1))
      = (∑ i ∈ Finset.range 372, stT249 (i+1)) + stT249 373 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 372
    simpa using h
  have hprev := st249_p372
  have hstep := st249_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p374 : ((4327758684711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT249 (i+1))
      = (∑ i ∈ Finset.range 373, stT249 (i+1)) + stT249 374 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 373
    simpa using h
  have hprev := st249_p373
  have hstep := st249_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p375 : ((4475217913649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT249 (i+1))
      = (∑ i ∈ Finset.range 374, stT249 (i+1)) + stT249 375 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 374
    simpa using h
  have hprev := st249_p374
  have hstep := st249_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p376 : ((2360780488587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT249 (i+1))
      = (∑ i ∈ Finset.range 375, stT249 (i+1)) + stT249 376 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 375
    simpa using h
  have hprev := st249_p375
  have hstep := st249_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p377 : ((4962410568457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT249 (i+1))
      = (∑ i ∈ Finset.range 376, stT249 (i+1)) + stT249 377 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 376
    simpa using h
  have hprev := st249_p376
  have hstep := st249_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p378 : ((1019347020893/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT249 (i+1))
      = (∑ i ∈ Finset.range 377, stT249 (i+1)) + stT249 378 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 377
    simpa using h
  have hprev := st249_p377
  have hstep := st249_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p379 : ((5068970943499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT249 (i+1))
      = (∑ i ∈ Finset.range 378, stT249 (i+1)) + stT249 379 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 378
    simpa using h
  have hprev := st249_p378
  have hstep := st249_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p380 : ((4891441007189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT249 (i+1))
      = (∑ i ∈ Finset.range 379, stT249 (i+1)) + stT249 380 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 379
    simpa using h
  have hprev := st249_p379
  have hstep := st249_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p381 : ((4638224469503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT249 (i+1))
      = (∑ i ∈ Finset.range 380, stT249 (i+1)) + stT249 381 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 380
    simpa using h
  have hprev := st249_p380
  have hstep := st249_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p382 : ((8827580222281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT249 (i+1))
      = (∑ i ∈ Finset.range 381, stT249 (i+1)) + stT249 382 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 381
    simpa using h
  have hprev := st249_p381
  have hstep := st249_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p383 : ((1723918633231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT249 (i+1))
      = (∑ i ∈ Finset.range 382, stT249 (i+1)) + stT249 383 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 382
    simpa using h
  have hprev := st249_p382
  have hstep := st249_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p384 : ((1747195199137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT249 (i+1))
      = (∑ i ∈ Finset.range 383, stT249 (i+1)) + stT249 384 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 383
    simpa using h
  have hprev := st249_p383
  have hstep := st249_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p385 : ((9128019911847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT249 (i+1))
      = (∑ i ∈ Finset.range 384, stT249 (i+1)) + stT249 385 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 384
    simpa using h
  have hprev := st249_p384
  have hstep := st249_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p386 : ((9636414979101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT249 (i+1))
      = (∑ i ∈ Finset.range 385, stT249 (i+1)) + stT249 386 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 385
    simpa using h
  have hprev := st249_p385
  have hstep := st249_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p387 : ((2011353127097/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT249 (i+1))
      = (∑ i ∈ Finset.range 386, stT249 (i+1)) + stT249 387 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 386
    simpa using h
  have hprev := st249_p386
  have hstep := st249_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p388 : ((5110892118231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT249 (i+1))
      = (∑ i ∈ Finset.range 387, stT249 (i+1)) + stT249 388 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 387
    simpa using h
  have hprev := st249_p387
  have hstep := st249_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p389 : ((2013435968799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT249 (i+1))
      = (∑ i ∈ Finset.range 388, stT249 (i+1)) + stT249 389 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 388
    simpa using h
  have hprev := st249_p388
  have hstep := st249_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p390 : ((1931106587061/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT249 (i+1))
      = (∑ i ∈ Finset.range 389, stT249 (i+1)) + stT249 390 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 389
    simpa using h
  have hprev := st249_p389
  have hstep := st249_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p391 : ((9149849875899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT249 (i+1))
      = (∑ i ∈ Finset.range 390, stT249 (i+1)) + stT249 391 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 390
    simpa using h
  have hprev := st249_p390
  have hstep := st249_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p392 : ((4374169709913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT249 (i+1))
      = (∑ i ∈ Finset.range 391, stT249 (i+1)) + stT249 392 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 391
    simpa using h
  have hprev := st249_p391
  have hstep := st249_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p393 : ((215169010837/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT249 (i+1))
      = (∑ i ∈ Finset.range 392, stT249 (i+1)) + stT249 393 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 392
    simpa using h
  have hprev := st249_p392
  have hstep := st249_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p394 : ((1097337639567/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT249 (i+1))
      = (∑ i ∈ Finset.range 393, stT249 (i+1)) + stT249 394 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 393
    simpa using h
  have hprev := st249_p393
  have hstep := st249_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p395 : ((4598203494243/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT249 (i+1))
      = (∑ i ∈ Finset.range 394, stT249 (i+1)) + stT249 395 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 394
    simpa using h
  have hprev := st249_p394
  have hstep := st249_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p396 : ((4849265507187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT249 (i+1))
      = (∑ i ∈ Finset.range 395, stT249 (i+1)) + stT249 396 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 395
    simpa using h
  have hprev := st249_p395
  have hstep := st249_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p397 : ((10093048258209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT249 (i+1))
      = (∑ i ∈ Finset.range 396, stT249 (i+1)) + stT249 397 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 396
    simpa using h
  have hprev := st249_p396
  have hstep := st249_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p398 : ((409224776941/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT249 (i+1))
      = (∑ i ∈ Finset.range 397, stT249 (i+1)) + stT249 398 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 397
    simpa using h
  have hprev := st249_p397
  have hstep := st249_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p399 : ((5030225900291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT249 (i+1))
      = (∑ i ∈ Finset.range 398, stT249 (i+1)) + stT249 399 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 398
    simpa using h
  have hprev := st249_p398
  have hstep := st249_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p400 : ((1205996496953/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT249 (i+1))
      = (∑ i ∈ Finset.range 399, stT249 (i+1)) + stT249 400 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 399
    simpa using h
  have hprev := st249_p399
  have hstep := st249_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p401 : ((4574339934857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT249 (i+1))
      = (∑ i ∈ Finset.range 400, stT249 (i+1)) + stT249 401 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 400
    simpa using h
  have hprev := st249_p400
  have hstep := st249_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p402 : ((8748942201109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT249 (i+1))
      = (∑ i ∈ Finset.range 401, stT249 (i+1)) + stT249 402 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 401
    simpa using h
  have hprev := st249_p401
  have hstep := st249_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p403 : ((8596470243549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT249 (i+1))
      = (∑ i ∈ Finset.range 402, stT249 (i+1)) + stT249 403 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 402
    simpa using h
  have hprev := st249_p402
  have hstep := st249_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p404 : ((8746354506301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT249 (i+1))
      = (∑ i ∈ Finset.range 403, stT249 (i+1)) + stT249 404 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 403
    simpa using h
  have hprev := st249_p403
  have hstep := st249_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p405 : ((285692565439/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT249 (i+1))
      = (∑ i ∈ Finset.range 404, stT249 (i+1)) + stT249 405 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 404
    simpa using h
  have hprev := st249_p404
  have hstep := st249_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p406 : ((4819061282121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT249 (i+1))
      = (∑ i ∈ Finset.range 405, stT249 (i+1)) + stT249 406 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 405
    simpa using h
  have hprev := st249_p405
  have hstep := st249_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p407 : ((10053407575809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT249 (i+1))
      = (∑ i ∈ Finset.range 406, stT249 (i+1)) + stT249 407 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 406
    simpa using h
  have hprev := st249_p406
  have hstep := st249_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p408 : ((5119036140087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT249 (i+1))
      = (∑ i ∈ Finset.range 407, stT249 (i+1)) + stT249 408 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 407
    simpa using h
  have hprev := st249_p407
  have hstep := st249_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p409 : ((5063321351043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT249 (i+1))
      = (∑ i ∈ Finset.range 408, stT249 (i+1)) + stT249 409 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 408
    simpa using h
  have hprev := st249_p408
  have hstep := st249_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p410 : ((9760414642011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT249 (i+1))
      = (∑ i ∈ Finset.range 409, stT249 (i+1)) + stT249 410 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 409
    simpa using h
  have hprev := st249_p409
  have hstep := st249_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p411 : ((1854243619391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT249 (i+1))
      = (∑ i ∈ Finset.range 410, stT249 (i+1)) + stT249 411 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 410
    simpa using h
  have hprev := st249_p410
  have hstep := st249_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p412 : ((1766668080189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT249 (i+1))
      = (∑ i ∈ Finset.range 411, stT249 (i+1)) + stT249 412 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 411
    simpa using h
  have hprev := st249_p411
  have hstep := st249_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p413 : ((8601314100701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT249 (i+1))
      = (∑ i ∈ Finset.range 412, stT249 (i+1)) + stT249 413 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 412
    simpa using h
  have hprev := st249_p412
  have hstep := st249_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p414 : ((8655833200591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT249 (i+1))
      = (∑ i ∈ Finset.range 413, stT249 (i+1)) + stT249 414 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 413
    simpa using h
  have hprev := st249_p413
  have hstep := st249_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p415 : ((8976504978511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT249 (i+1))
      = (∑ i ∈ Finset.range 414, stT249 (i+1)) + stT249 415 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 414
    simpa using h
  have hprev := st249_p414
  have hstep := st249_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p416 : ((9450344768431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT249 (i+1))
      = (∑ i ∈ Finset.range 415, stT249 (i+1)) + stT249 416 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 415
    simpa using h
  have hprev := st249_p415
  have hstep := st249_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p417 : ((9912271360693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT249 (i+1))
      = (∑ i ∈ Finset.range 416, stT249 (i+1)) + stT249 417 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 416
    simpa using h
  have hprev := st249_p416
  have hstep := st249_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p418 : ((10202821322373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT249 (i+1))
      = (∑ i ∈ Finset.range 417, stT249 (i+1)) + stT249 418 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 417
    simpa using h
  have hprev := st249_p417
  have hstep := st249_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p419 : ((511144435513/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT249 (i+1))
      = (∑ i ∈ Finset.range 418, stT249 (i+1)) + stT249 419 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 418
    simpa using h
  have hprev := st249_p418
  have hstep := st249_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p420 : ((4983404548877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT249 (i+1))
      = (∑ i ∈ Finset.range 419, stT249 (i+1)) + stT249 420 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 419
    simpa using h
  have hprev := st249_p419
  have hstep := st249_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p421 : ((952301686309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT249 (i+1))
      = (∑ i ∈ Finset.range 420, stT249 (i+1)) + stT249 421 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 420
    simpa using h
  have hprev := st249_p420
  have hstep := st249_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p422 : ((1808554732581/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT249 (i+1))
      = (∑ i ∈ Finset.range 421, stT249 (i+1)) + stT249 422 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 421
    simpa using h
  have hprev := st249_p421
  have hstep := st249_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p423 : ((4344136667211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT249 (i+1))
      = (∑ i ∈ Finset.range 422, stT249 (i+1)) + stT249 423 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 422
    simpa using h
  have hprev := st249_p422
  have hstep := st249_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p424 : ((8578021203633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT249 (i+1))
      = (∑ i ∈ Finset.range 423, stT249 (i+1)) + stT249 424 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 423
    simpa using h
  have hprev := st249_p423
  have hstep := st249_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p425 : ((8747785382071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT249 (i+1))
      = (∑ i ∈ Finset.range 424, stT249 (i+1)) + stT249 425 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 424
    simpa using h
  have hprev := st249_p424
  have hstep := st249_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p426 : ((285619461179/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT249 (i+1))
      = (∑ i ∈ Finset.range 425, stT249 (i+1)) + stT249 426 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 425
    simpa using h
  have hprev := st249_p425
  have hstep := st249_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p427 : ((9623259726403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT249 (i+1))
      = (∑ i ∈ Finset.range 426, stT249 (i+1)) + stT249 427 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 426
    simpa using h
  have hprev := st249_p426
  have hstep := st249_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p428 : ((10038253389331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT249 (i+1))
      = (∑ i ∈ Finset.range 427, stT249 (i+1)) + stT249 428 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 427
    simpa using h
  have hprev := st249_p427
  have hstep := st249_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p429 : ((10248844769267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT249 (i+1))
      = (∑ i ∈ Finset.range 428, stT249 (i+1)) + stT249 429 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 428
    simpa using h
  have hprev := st249_p428
  have hstep := st249_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p430 : ((5093550393381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT249 (i+1))
      = (∑ i ∈ Finset.range 429, stT249 (i+1)) + stT249 430 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 429
    simpa using h
  have hprev := st249_p429
  have hstep := st249_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p431 : ((4937150247843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT249 (i+1))
      = (∑ i ∈ Finset.range 430, stT249 (i+1)) + stT249 431 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 430
    simpa using h
  have hprev := st249_p430
  have hstep := st249_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p432 : ((235320820573/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT249 (i+1))
      = (∑ i ∈ Finset.range 431, stT249 (i+1)) + stT249 432 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 431
    simpa using h
  have hprev := st249_p431
  have hstep := st249_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p433 : ((179042582123/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT249 (i+1))
      = (∑ i ∈ Finset.range 432, stT249 (i+1)) + stT249 433 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 432
    simpa using h
  have hprev := st249_p432
  have hstep := st249_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p434 : ((864005630407/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT249 (i+1))
      = (∑ i ∈ Finset.range 433, stT249 (i+1)) + stT249 434 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 433
    simpa using h
  have hprev := st249_p433
  have hstep := st249_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p435 : ((857568346743/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT249 (i+1))
      = (∑ i ∈ Finset.range 434, stT249 (i+1)) + stT249 435 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 434
    simpa using h
  have hprev := st249_p434
  have hstep := st249_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p436 : ((1097300797813/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT249 (i+1))
      = (∑ i ∈ Finset.range 435, stT249 (i+1)) + stT249 436 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 435
    simpa using h
  have hprev := st249_p435
  have hstep := st249_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p437 : ((1147857175517/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT249 (i+1))
      = (∑ i ∈ Finset.range 436, stT249 (i+1)) + stT249 437 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 436
    simpa using h
  have hprev := st249_p436
  have hstep := st249_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p438 : ((37736886377/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT249 (i+1))
      = (∑ i ∈ Finset.range 437, stT249 (i+1)) + stT249 438 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 437
    simpa using h
  have hprev := st249_p437
  have hstep := st249_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p439 : ((10061458209731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT249 (i+1))
      = (∑ i ∈ Finset.range 438, stT249 (i+1)) + stT249 439 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 438
    simpa using h
  have hprev := st249_p438
  have hstep := st249_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p440 : ((5130184964451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT249 (i+1))
      = (∑ i ∈ Finset.range 439, stT249 (i+1)) + stT249 440 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 439
    simpa using h
  have hprev := st249_p439
  have hstep := st249_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p441 : ((10196353191817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT249 (i+1))
      = (∑ i ∈ Finset.range 440, stT249 (i+1)) + stT249 441 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 440
    simpa using h
  have hprev := st249_p440
  have hstep := st249_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p442 : ((9890351039353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT249 (i+1))
      = (∑ i ∈ Finset.range 441, stT249 (i+1)) + stT249 442 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 441
    simpa using h
  have hprev := st249_p441
  have hstep := st249_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p443 : ((9437758390813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT249 (i+1))
      = (∑ i ∈ Finset.range 442, stT249 (i+1)) + stT249 443 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 442
    simpa using h
  have hprev := st249_p442
  have hstep := st249_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p444 : ((8978161849843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT249 (i+1))
      = (∑ i ∈ Finset.range 443, stT249 (i+1)) + stT249 444 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 443
    simpa using h
  have hprev := st249_p443
  have hstep := st249_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p445 : ((8652080301869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT249 (i+1))
      = (∑ i ∈ Finset.range 444, stT249 (i+1)) + stT249 445 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 444
    simpa using h
  have hprev := st249_p444
  have hstep := st249_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p446 : ((8558192892977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT249 (i+1))
      = (∑ i ∈ Finset.range 445, stT249 (i+1)) + stT249 446 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 445
    simpa using h
  have hprev := st249_p445
  have hstep := st249_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p447 : ((348958104929/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT249 (i+1))
      = (∑ i ∈ Finset.range 446, stT249 (i+1)) + stT249 447 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 446
    simpa using h
  have hprev := st249_p446
  have hstep := st249_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p448 : ((909824989997/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT249 (i+1))
      = (∑ i ∈ Finset.range 447, stT249 (i+1)) + stT249 448 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 447
    simpa using h
  have hprev := st249_p447
  have hstep := st249_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p449 : ((597984161119/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT249 (i+1))
      = (∑ i ∈ Finset.range 448, stT249 (i+1)) + stT249 449 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 448
    simpa using h
  have hprev := st249_p448
  have hstep := st249_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p450 : ((2497901546169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT249 (i+1))
      = (∑ i ∈ Finset.range 449, stT249 (i+1)) + stT249 450 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 449
    simpa using h
  have hprev := st249_p449
  have hstep := st249_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p451 : ((10243775673963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT249 (i+1))
      = (∑ i ∈ Finset.range 450, stT249 (i+1)) + stT249 451 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 450
    simpa using h
  have hprev := st249_p450
  have hstep := st249_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p452 : ((10250198439763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT249 (i+1))
      = (∑ i ∈ Finset.range 451, stT249 (i+1)) + stT249 452 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 451
    simpa using h
  have hprev := st249_p451
  have hstep := st249_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p453 : ((10009990349149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT249 (i+1))
      = (∑ i ∈ Finset.range 452, stT249 (i+1)) + stT249 453 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 452
    simpa using h
  have hprev := st249_p452
  have hstep := st249_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p454 : ((9594804280521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT249 (i+1))
      = (∑ i ∈ Finset.range 453, stT249 (i+1)) + stT249 454 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 453
    simpa using h
  have hprev := st249_p453
  have hstep := st249_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p455 : ((9126894516649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT249 (i+1))
      = (∑ i ∈ Finset.range 454, stT249 (i+1)) + stT249 455 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 454
    simpa using h
  have hprev := st249_p454
  have hstep := st249_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p456 : ((874286475419/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT249 (i+1))
      = (∑ i ∈ Finset.range 455, stT249 (i+1)) + stT249 456 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 455
    simpa using h
  have hprev := st249_p455
  have hstep := st249_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p457 : ((2138452297979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT249 (i+1))
      = (∑ i ∈ Finset.range 456, stT249 (i+1)) + stT249 457 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 456
    simpa using h
  have hprev := st249_p456
  have hstep := st249_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p458 : ((2153389018833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT249 (i+1))
      = (∑ i ∈ Finset.range 457, stT249 (i+1)) + stT249 458 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 457
    simpa using h
  have hprev := st249_p457
  have hstep := st249_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p459 : ((2225970315523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT249 (i+1))
      = (∑ i ∈ Finset.range 458, stT249 (i+1)) + stT249 459 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 458
    simpa using h
  have hprev := st249_p458
  have hstep := st249_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p460 : ((2335155110749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT249 (i+1))
      = (∑ i ∈ Finset.range 459, stT249 (i+1)) + stT249 460 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 459
    simpa using h
  have hprev := st249_p459
  have hstep := st249_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p461 : ((153102377447/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT249 (i+1))
      = (∑ i ∈ Finset.range 460, stT249 (i+1)) + stT249 461 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 460
    simpa using h
  have hprev := st249_p460
  have hstep := st249_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p462 : ((2536867890079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT249 (i+1))
      = (∑ i ∈ Finset.range 461, stT249 (i+1)) + stT249 462 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 461
    simpa using h
  have hprev := st249_p461
  have hstep := st249_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p463 : ((10289092870003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT249 (i+1))
      = (∑ i ∈ Finset.range 462, stT249 (i+1)) + stT249 463 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 462
    simpa using h
  have hprev := st249_p462
  have hstep := st249_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p464 : ((5092180507921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT249 (i+1))
      = (∑ i ∈ Finset.range 463, stT249 (i+1)) + stT249 464 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 463
    simpa using h
  have hprev := st249_p463
  have hstep := st249_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p465 : ((9863657209263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT249 (i+1))
      = (∑ i ∈ Finset.range 464, stT249 (i+1)) + stT249 465 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 464
    simpa using h
  have hprev := st249_p464
  have hstep := st249_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p466 : ((9417462051621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT249 (i+1))
      = (∑ i ∈ Finset.range 465, stT249 (i+1)) + stT249 466 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 465
    simpa using h
  have hprev := st249_p465
  have hstep := st249_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p467 : ((1121302306527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT249 (i+1))
      = (∑ i ∈ Finset.range 466, stT249 (i+1)) + stT249 467 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 466
    simpa using h
  have hprev := st249_p466
  have hstep := st249_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p468 : ((1729275083291/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT249 (i+1))
      = (∑ i ∈ Finset.range 467, stT249 (i+1)) + stT249 468 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 467
    simpa using h
  have hprev := st249_p467
  have hstep := st249_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p469 : ((8534236100881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT249 (i+1))
      = (∑ i ∈ Finset.range 468, stT249 (i+1)) + stT249 469 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 468
    simpa using h
  have hprev := st249_p468
  have hstep := st249_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p470 : ((2165985378139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT249 (i+1))
      = (∑ i ∈ Finset.range 469, stT249 (i+1)) + stT249 470 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 469
    simpa using h
  have hprev := st249_p469
  have hstep := st249_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p471 : ((4499509928603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT249 (i+1))
      = (∑ i ∈ Finset.range 470, stT249 (i+1)) + stT249 471 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 470
    simpa using h
  have hprev := st249_p470
  have hstep := st249_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p472 : ((9447332490901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT249 (i+1))
      = (∑ i ∈ Finset.range 471, stT249 (i+1)) + stT249 472 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 471
    simpa using h
  have hprev := st249_p471
  have hstep := st249_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p473 : ((9886761971501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT249 (i+1))
      = (∑ i ∈ Finset.range 472, stT249 (i+1)) + stT249 473 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 472
    simpa using h
  have hprev := st249_p472
  have hstep := st249_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p474 : ((10198580820071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT249 (i+1))
      = (∑ i ∈ Finset.range 473, stT249 (i+1)) + stT249 474 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 473
    simpa using h
  have hprev := st249_p473
  have hstep := st249_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p475 : ((10299374978827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT249 (i+1))
      = (∑ i ∈ Finset.range 474, stT249 (i+1)) + stT249 475 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 474
    simpa using h
  have hprev := st249_p474
  have hstep := st249_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p476 : ((10162975519027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT249 (i+1))
      = (∑ i ∈ Finset.range 475, stT249 (i+1)) + stT249 476 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 475
    simpa using h
  have hprev := st249_p475
  have hstep := st249_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p477 : ((9826730261497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT249 (i+1))
      = (∑ i ∈ Finset.range 476, stT249 (i+1)) + stT249 477 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 476
    simpa using h
  have hprev := st249_p476
  have hstep := st249_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p478 : ((9380810687917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT249 (i+1))
      = (∑ i ∈ Finset.range 477, stT249 (i+1)) + stT249 478 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 477
    simpa using h
  have hprev := st249_p477
  have hstep := st249_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p479 : ((1788741530153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT249 (i+1))
      = (∑ i ∈ Finset.range 478, stT249 (i+1)) + stT249 479 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 478
    simpa using h
  have hprev := st249_p478
  have hstep := st249_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p480 : ((8630637741929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT249 (i+1))
      = (∑ i ∈ Finset.range 479, stT249 (i+1)) + stT249 480 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 479
    simpa using h
  have hprev := st249_p479
  have hstep := st249_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p481 : ((8523304522529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT249 (i+1))
      = (∑ i ∈ Finset.range 480, stT249 (i+1)) + stT249 481 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 480
    simpa using h
  have hprev := st249_p480
  have hstep := st249_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p482 : ((8648969741933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT249 (i+1))
      = (∑ i ∈ Finset.range 481, stT249 (i+1)) + stT249 482 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 481
    simpa using h
  have hprev := st249_p481
  have hstep := st249_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p483 : ((2243490937667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT249 (i+1))
      = (∑ i ∈ Finset.range 482, stT249 (i+1)) + stT249 483 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 482
    simpa using h
  have hprev := st249_p482
  have hstep := st249_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p484 : ((9413189220533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT249 (i+1))
      = (∑ i ∈ Finset.range 483, stT249 (i+1)) + stT249 484 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 483
    simpa using h
  have hprev := st249_p483
  have hstep := st249_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p485 : ((9852703003213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT249 (i+1))
      = (∑ i ∈ Finset.range 484, stT249 (i+1)) + stT249 485 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 484
    simpa using h
  have hprev := st249_p484
  have hstep := st249_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p486 : ((10179392205013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT249 (i+1))
      = (∑ i ∈ Finset.range 485, stT249 (i+1)) + stT249 486 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 485
    simpa using h
  have hprev := st249_p485
  have hstep := st249_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p487 : ((5154982000517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT249 (i+1))
      = (∑ i ∈ Finset.range 486, stT249 (i+1)) + stT249 487 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 486
    simpa using h
  have hprev := st249_p486
  have hstep := st249_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p488 : ((5105923366571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT249 (i+1))
      = (∑ i ∈ Finset.range 487, stT249 (i+1)) + stT249 488 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 487
    simpa using h
  have hprev := st249_p487
  have hstep := st249_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p489 : ((991088477531/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT249 (i+1))
      = (∑ i ∈ Finset.range 488, stT249 (i+1)) + stT249 489 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 488
    simpa using h
  have hprev := st249_p488
  have hstep := st249_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p490 : ((59275436593/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT249 (i+1))
      = (∑ i ∈ Finset.range 489, stT249 (i+1)) + stT249 490 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 489
    simpa using h
  have hprev := st249_p489
  have hstep := st249_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p491 : ((903954300841/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT249 (i+1))
      = (∑ i ∈ Finset.range 490, stT249 (i+1)) + stT249 491 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 490
    simpa using h
  have hprev := st249_p490
  have hstep := st249_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p492 : ((1737809439703/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT249 (i+1))
      = (∑ i ∈ Finset.range 491, stT249 (i+1)) + stT249 492 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 491
    simpa using h
  have hprev := st249_p491
  have hstep := st249_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p493 : ((1703981998501/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT249 (i+1))
      = (∑ i ∈ Finset.range 492, stT249 (i+1)) + stT249 493 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 492
    simpa using h
  have hprev := st249_p492
  have hstep := st249_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p494 : ((2143397179313/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT249 (i+1))
      = (∑ i ∈ Finset.range 493, stT249 (i+1)) + stT249 494 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 493
    simpa using h
  have hprev := st249_p493
  have hstep := st249_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p495 : ((1104484999393/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT249 (i+1))
      = (∑ i ∈ Finset.range 494, stT249 (i+1)) + stT249 495 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 494
    simpa using h
  have hprev := st249_p494
  have hstep := st249_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p496 : ((288785100247/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT249 (i+1))
      = (∑ i ∈ Finset.range 495, stT249 (i+1)) + stT249 496 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 495
    simpa using h
  have hprev := st249_p495
  have hstep := st249_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p497 : ((9688948119303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT249 (i+1))
      = (∑ i ∈ Finset.range 496, stT249 (i+1)) + stT249 497 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 496
    simpa using h
  have hprev := st249_p496
  have hstep := st249_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p498 : ((10069323604143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT249 (i+1))
      = (∑ i ∈ Finset.range 497, stT249 (i+1)) + stT249 498 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 497
    simpa using h
  have hprev := st249_p497
  have hstep := st249_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p499 : ((5144777231021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT249 (i+1))
      = (∑ i ∈ Finset.range 498, stT249 (i+1)) + stT249 499 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 498
    simpa using h
  have hprev := st249_p498
  have hstep := st249_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_p500 : ((10296641446453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT249 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT249 (i+1))
      = (∑ i ∈ Finset.range 499, stT249 (i+1)) + stT249 500 := by
    have h := Finset.sum_range_succ (fun i => stT249 (i+1)) 499
    simpa using h
  have hprev := st249_p499
  have hstep := st249_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st249_s500 :
    |Real.sin (((249 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((5473/25000 : ℚ) : ℝ))
      - ((499937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 3887247/10000000) (δ := 2507/200000000) (ψ := 5473/25000) 249 246
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 249`** (evaluated boundary). -/
theorem station_249_sign : 0 < hardyG ((((249:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 249 500 (by norm_num) (by norm_num)
    ((5473/25000 : ℚ) : ℝ)
  have hchain := st249_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT249 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((249 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((5473/25000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st249_c500
  have hsinb := abs_le.mp st249_s500
  have hbdy_lo : ((-111351388783093/1240025000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((249 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((5473/25000 : ℚ) : ℝ))) / 2
          - ((((249:ℕ)):ℝ))
            * Real.sin (((249 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((5473/25000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((249:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((249:ℝ) * Real.log (500:ℝ) - ((5473/25000 : ℚ) : ℝ))) / 2
        - ((249:ℝ)) * Real.sin ((249:ℝ) * Real.log (500:ℝ) - ((5473/25000 : ℚ) : ℝ))
        ≥ ((-497978099/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((249:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-497978099/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-497978099/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-497978099/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((249:ℕ)):ℝ))+1) * (((((249:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((58977017071/120000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((10296641446453/10000000000000 : ℚ) : ℝ) + ((-111351388783093/1240025000000000 : ℚ) : ℝ)
      - ((58977017071/120000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((5473/25000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((249:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((5473/25000 : ℚ) : ℝ)
        * (riemannZeta (line ((((249:ℕ)):ℝ)))).re
      - Real.sin ((5473/25000 : ℚ) : ℝ)
        * (riemannZeta (line ((((249:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((249:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((249:ℕ)):ℝ))
      = (((((249:ℕ)):ℝ)) * (Real.log ((((249:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((249:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_249
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
  have hθwin : |(((5473/25000 : ℚ) : ℝ) + ((53:ℤ)) * (2*Real.pi)) - theta ((((249:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((249:ℕ)):ℝ)))
    (φ := ((5473/25000 : ℚ) : ℝ) + ((53:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((5473/25000 : ℚ)) : ℝ) 53).1,
    (cos_sin_shift (((5473/25000 : ℚ)) : ℝ) 53).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_249_sign
end AxiomAudit
