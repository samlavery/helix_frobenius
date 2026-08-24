import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 76` (rung-81; thin window, evaluated boundary, N = 200)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT76 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((76 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-106277/500000 : ℚ) : ℝ))

theorem st76_c1 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((195499/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66423/1250000) (δ := 41/100000000) (ψ := -106277/500000) 76 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t1 : ((195489/200000 : ℚ) : ℝ) ≤ stT76 1 := by
  have hc : ((195489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195489/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((195489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c2 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-870127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6565643/10000000) (δ := 607/100000000) (ψ := -106277/500000) 76 8
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t2 : ((-1538270184759/2500000000000 : ℚ) : ℝ) ≤ stT76 2 := by
  have hc : ((-870177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1538270184759/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-870177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c3 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-439357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5064197/10000000) (δ := 661/100000000) (ψ := -106277/500000) 76 13
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t3 : ((-2536917632721/10000000000000 : ℚ) : ℝ) ≤ stT76 3 := by
  have hc : ((-439407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2536917632721/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-439407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c4 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((64349/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1554031/5000000) (δ := 29/6250000) (ψ := -106277/500000) 76 17
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t4 : ((64339/400000 : ℚ) : ℝ) ≤ stT76 4 := by
  have hc : ((64339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64339/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((64339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c5 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-99997/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7834677/10000000) (δ := 667/100000000) (ψ := -106277/500000) 76 20
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t5 : ((-27951409017/62500000000 : ℚ) : ℝ) ≤ stT76 5 := by
  have hc : ((-50001/50000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27951409017/62500000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-50001/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c6 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-67407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1152377/2500000) (δ := 517/100000000) (ψ := -106277/500000) 76 22
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t6 : ((-550477925237/5000000000000 : ℚ) : ℝ) ≤ stT76 6 := by
  have hc : ((-134839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550477925237/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-134839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c7 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-225451/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3368403/5000000) (δ := 53/12500000) (ψ := -106277/500000) 76 24
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t7 : ((-340868796183/1000000000000 : ℚ) : ℝ) ≤ stT76 7 := by
  have hc : ((-450927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340868796183/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-450927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c8 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((389711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731549/2500000) (δ := 227/50000000) (ψ := -106277/500000) 76 25
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t8 : ((1377659324313/10000000000000 : ℚ) : ℝ) ≤ stT76 8 := by
  have hc : ((389661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1377659324313/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((389661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c9 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-191659/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3055477/5000000) (δ := 571/100000000) (ψ := -106277/500000) 76 27
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t9 : ((-638905127781/2500000000000 : ℚ) : ℝ) ≤ stT76 9 := by
  have hc : ((-383343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638905127781/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-383343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c10 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((150339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1800419/10000000) (δ := 351/50000000) (ψ := -106277/500000) 76 28
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t10 : ((475381939133/2000000000000 : ℚ) : ℝ) ≤ stT76 10 := by
  have hc : ((150329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475381939133/2000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((150329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c11 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((194257/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75069/1250000) (δ := 69/12500000) (ψ := -106277/500000) 76 29
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t11 : ((585676654911/2000000000000 : ℚ) : ℝ) ≤ stT76 11 := by
  have hc : ((194247/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((585676654911/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((194247/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c12 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((168391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5699/40000) (δ := 1/250000) (ψ := -106277/500000) 76 30
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t12 : ((486074020131/2000000000000 : ℚ) : ℝ) ≤ stT76 12 := by
  have hc : ((168381/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486074020131/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((168381/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c13 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((466171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 924901/10000000) (δ := 207/50000000) (ψ := -106277/500000) 76 31
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t13 : ((1292855931/5000000000 : ℚ) : ℝ) ≤ stT76 13 := by
  have hc : ((233073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1292855931/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((233073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c14 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((960773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702547/10000000) (δ := 539/100000000) (ψ := -106277/500000) 76 32
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t14 : ((641909954619/2500000000000 : ℚ) : ℝ) ≤ stT76 14 := by
  have hc : ((960723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((641909954619/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((960723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c15 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((247453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660373/2000000) (δ := 3/390625) (ψ := -106277/500000) 76 33
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t15 : ((159697894291/2500000000000 : ℚ) : ℝ) ≤ stT76 15 := by
  have hc : ((247403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159697894291/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((247403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c16 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-451823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6747509/10000000) (δ := 597/100000000) (ψ := -106277/500000) 76 34
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t16 : ((-141202556481/625000000000 : ℚ) : ℝ) ≤ stT76 16 := by
  have hc : ((-56481/62500 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141202556481/625000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-56481/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c17 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-331291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4771169/10000000) (δ := 437/100000000) (ψ := -106277/500000) 76 34
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t17 : ((-803620213737/10000000000000 : ℚ) : ℝ) ≤ stT76 17 := by
  have hc : ((-331341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-803620213737/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-331341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c18 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((999529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9587/1250000) (δ := 417/100000000) (ψ := -106277/500000) 76 35
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t18 : ((1177896995769/5000000000000 : ℚ) : ℝ) ≤ stT76 18 := by
  have hc : ((999479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1177896995769/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((999479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c19 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-592339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5511887/10000000) (δ := 587/100000000) (ψ := -106277/500000) 76 36
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t19 : ((-679516981731/5000000000000 : ℚ) : ℝ) ≤ stT76 19 := by
  have hc : ((-592389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-679516981731/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-592389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c20 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-122431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4233839/10000000) (δ := 547/100000000) (ψ := -106277/500000) 76 36
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t20 : ((-68468961177/2500000000000 : ℚ) : ℝ) ≤ stT76 20 := by
  have hc : ((-122481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68468961177/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-122481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c21 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((635919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2203993/10000000) (δ := 97/20000000) (ψ := -106277/500000) 76 37
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t21 : ((693789671341/5000000000000 : ℚ) : ℝ) ≤ stT76 21 := by
  have hc : ((635869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((693789671341/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((635869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c22 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-220857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 663481/1000000) (δ := 199/50000000) (ψ := -106277/500000) 76 37
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t22 : ((-117723885239/625000000000 : ℚ) : ℝ) ≤ stT76 22 := by
  have hc : ((-441739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117723885239/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-441739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c23 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((968683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627319/10000000) (δ := 337/50000000) (ψ := -106277/500000) 76 38
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t23 : ((252467411019/1250000000000 : ℚ) : ℝ) ≤ stT76 23 := by
  have hc : ((968633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252467411019/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((968633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c24 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-493773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116547/156250) (δ := 277/50000000) (ψ := -106277/500000) 76 38
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t24 : ((-251990304279/1250000000000 : ℚ) : ℝ) ≤ stT76 24 := by
  have hc : ((-246899/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251990304279/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-246899/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c25 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((980637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61597/1250000) (δ := 583/100000000) (ψ := -106277/500000) 76 39
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t25 : ((980587/5000000 : ℚ) : ℝ) ≤ stT76 25 := by
  have hc : ((980587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((980587/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((980587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c26 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-58539/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6959159/10000000) (δ := 503/100000000) (ψ := -106277/500000) 76 39
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t26 : ((-459242363797/2500000000000 : ℚ) : ℝ) ≤ stT76 26 := by
  have hc : ((-468337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459242363797/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-468337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c27 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((403643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -789071/5000000) (δ := 47/10000000) (ψ := -106277/500000) 76 40
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t27 : ((776762841/5000000000 : ℚ) : ℝ) ≤ stT76 27 := by
  have hc : ((201809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((776762841/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((201809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c28 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-106557/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5331711/10000000) (δ := 693/100000000) (ψ := -106277/500000) 76 40
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t28 : ((-201392767641/2000000000000 : ℚ) : ℝ) ≤ stT76 28 := by
  have hc : ((-106567/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201392767641/2000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-106567/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c29 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((697/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1854451/5000000) (δ := 281/50000000) (ψ := -106277/500000) 76 41
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t29 : ((6467767299/400000000000 : ℚ) : ℝ) ≤ stT76 29 := by
  have hc : ((3483/40000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6467767299/400000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((3483/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c30 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((459861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2732393/10000000) (δ := 601/100000000) (ψ := -106277/500000) 76 41
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t30 : ((839495794951/10000000000000 : ℚ) : ℝ) ≤ stT76 30 := by
  have hc : ((459811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((839495794951/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((459811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c31 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-451651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210797/312500) (δ := 751/100000000) (ψ := -106277/500000) 76 42
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t31 : ((-101404310813/625000000000 : ℚ) : ℝ) ≤ stT76 31 := by
  have hc : ((-112919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101404310813/625000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-112919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c32 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((959577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -713251/10000000) (δ := 751/100000000) (ψ := -106277/500000) 76 42
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t32 : ((848109603341/5000000000000 : ℚ) : ℝ) ≤ stT76 32 := by
  have hc : ((959527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((848109603341/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((959527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c33 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-464039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1283341/2500000) (δ := 113/25000000) (ψ := -106277/500000) 76 42
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t33 : ((-807875457153/10000000000000 : ℚ) : ℝ) ≤ stT76 33 := by
  have hc : ((-464089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-807875457153/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-464089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c34 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-38039/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -612817/1250000) (δ := 581/100000000) (ψ := -106277/500000) 76 43
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t34 : ((-8155615923/125000000000 : ℚ) : ℝ) ≤ stT76 34 := by
  have hc : ((-9511/25000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8155615923/125000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-9511/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c35 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((970851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75637/1250000) (δ := 231/50000000) (ψ := -106277/500000) 76 43
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t35 : ((410238174177/2500000000000 : ℚ) : ℝ) ≤ stT76 35 := by
  have hc : ((970801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410238174177/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((970801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c36 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-362911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2978781/5000000) (δ := 501/100000000) (ψ := -106277/500000) 76 43
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t36 : ((-75611681789/625000000000 : ℚ) : ℝ) ≤ stT76 36 := by
  have hc : ((-45367/62500 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75611681789/625000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-45367/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c37 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-244537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1136149/2500000) (δ := 69/10000000) (ψ := -106277/500000) 76 44
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t37 : ((-40209858213/1000000000000 : ℚ) : ℝ) ≤ stT76 37 := by
  have hc : ((-244587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40209858213/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-244587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c38 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((3913/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522371/10000000) (δ := 433/100000000) (ψ := -106277/500000) 76 44
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t38 : ((3967124337/25000000000 : ℚ) : ℝ) ≤ stT76 38 := by
  have hc : ((4891/5000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3967124337/25000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((4891/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c39 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-287371/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5457713/10000000) (δ := 9/2000000) (ψ := -106277/500000) 76 44
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t39 : ((-57525255209/625000000000 : ℚ) : ℝ) ≤ stT76 39 := by
  have hc : ((-71849/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57525255209/625000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-71849/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c40 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-284443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2719933/5000000) (δ := 101/25000000) (ψ := -106277/500000) 76 45
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t40 : ((-112445862263/1250000000000 : ℚ) : ℝ) ≤ stT76 40 := by
  have hc : ((-71117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112445862263/1250000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-71117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c41 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((955541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74827/1000000) (δ := 121/25000000) (ψ := -106277/500000) 76 45
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t41 : ((1492225647867/10000000000000 : ℚ) : ℝ) ≤ stT76 41 := by
  have hc : ((955491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1492225647867/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((955491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c42 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((38681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 766053/2000000) (δ := 639/100000000) (ψ := -106277/500000) 76 45
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t42 : ((59608907823/10000000000000 : ℚ) : ℝ) ≤ stT76 42 := by
  have hc : ((38631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59608907823/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((38631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c43 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-246013/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -925863/1250000) (δ := 167/25000000) (ψ := -106277/500000) 76 46
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t43 : ((-375185443143/2500000000000 : ℚ) : ℝ) ≤ stT76 43 := by
  have hc : ((-492051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375185443143/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-492051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c44 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((173907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -607779/2000000) (δ := 127/25000000) (ψ := -106277/500000) 76 46
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t44 : ((32767106549/625000000000 : ℚ) : ℝ) ≤ stT76 44 := by
  have hc : ((86941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32767106549/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((86941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c45 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((881211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1230947/10000000) (δ := 131/20000000) (ψ := -106277/500000) 76 46
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t45 : ((1313556395471/10000000000000 : ℚ) : ℝ) ≤ stT76 45 := by
  have hc : ((881161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1313556395471/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((881161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c46 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-111601/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270347/500000) (δ := 147/20000000) (ψ := -106277/500000) 76 46
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t46 : ((-8228074531/100000000000 : ℚ) : ℝ) ≤ stT76 46 := by
  have hc : ((-111611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8228074531/100000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-111611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c47 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-792649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1242969/2000000) (δ := 389/50000000) (ψ := -106277/500000) 76 47
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t47 : ((-23125407927/200000000000 : ℚ) : ℝ) ≤ stT76 47 := by
  have hc : ((-792699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23125407927/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-792699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c48 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((632609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2214697/10000000) (δ := 349/50000000) (ψ := -106277/500000) 76 47
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t48 : ((7304158773/80000000000 : ℚ) : ℝ) ≤ stT76 48 := by
  have hc : ((632559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7304158773/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((632559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c49 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((388413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212871/1250000) (δ := 149/20000000) (ψ := -106277/500000) 76 47
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t49 : ((138709958387/1250000000000 : ℚ) : ℝ) ≤ stT76 49 := by
  have hc : ((97097/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138709958387/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((97097/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c50 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-120367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2770741/5000000) (δ := 369/50000000) (ψ := -106277/500000) 76 47
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t50 : ((-85119419339/1000000000000 : ℚ) : ℝ) ≤ stT76 50 := by
  have hc : ((-120377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85119419339/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-120377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c51 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-836463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3201991/5000000) (δ := 527/100000000) (ψ := -106277/500000) 76 48
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t51 : ((-1171353260153/10000000000000 : ℚ) : ℝ) ≤ stT76 51 := by
  have hc : ((-836513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1171353260153/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-836513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c52 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((466189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357273/5000000) (δ := 647/100000000) (ψ := -106277/500000) 76 48
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t52 : ((2585673033/40000000000 : ℚ) : ℝ) ≤ stT76 52 := by
  have hc : ((466139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2585673033/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((466139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c53 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((187049/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904611/10000000) (δ := 687/100000000) (ψ := -106277/500000) 76 48
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t53 : ((51383541119/400000000000 : ℚ) : ℝ) ≤ stT76 53 := by
  have hc : ((187039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51383541119/400000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((187039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c54 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-210073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1114029/2500000) (δ := 447/100000000) (ψ := -106277/500000) 76 48
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t54 : ((-71485315461/2500000000000 : ℚ) : ℝ) ≤ stT76 54 := by
  have hc : ((-210123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71485315461/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-210123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c55 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-499687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -776551/1000000) (δ := 647/100000000) (ψ := -106277/500000) 76 49
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t55 : ((-6580192/48828125 : ℚ) : ℝ) ≤ stT76 55 := by
  have hc : ((-15616/15625 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6580192/48828125 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-15616/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c56 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-4131/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2170997/5000000) (δ := 687/100000000) (ψ := -106277/500000) 76 49
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t56 : ((-22087818403/1000000000000 : ℚ) : ℝ) ≤ stT76 56 := by
  have hc : ((-16529/100000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22087818403/1000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-16529/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c57 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((14442/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -39163/400000) (δ := 487/100000000) (ψ := -106277/500000) 76 49
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t57 : ((153022850827/1250000000000 : ℚ) : ℝ) ≤ stT76 57 := by
  have hc : ((462119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153022850827/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((462119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c58 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((14943/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 581339/2500000) (δ := 179/25000000) (ψ := -106277/500000) 76 49
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t58 : ((9809737011/125000000000 : ℚ) : ℝ) ≤ stT76 58 := by
  have hc : ((59767/100000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9809737011/125000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((59767/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c59 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-12239/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5573299/10000000) (δ := 109/25000000) (ψ := -106277/500000) 76 49
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t59 : ((-19918917/250000000 : ℚ) : ℝ) ≤ stT76 59 := by
  have hc : ((-153/250 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19918917/250000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-153/250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c60 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-9341/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54229/78125) (δ := 457/100000000) (ψ := -106277/500000) 76 50
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t60 : ((-4823931917/40000000000 : ℚ) : ℝ) ≤ stT76 60 := by
  have hc : ((-18683/20000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4823931917/40000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-18683/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c61 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((50477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -760149/2000000) (δ := 457/100000000) (ψ := -106277/500000) 76 50
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t61 : ((4035319821/625000000000 : ℚ) : ℝ) ≤ stT76 61 := by
  have hc : ((50427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4035319821/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((50427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c62 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((959803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355623/5000000) (δ := 617/100000000) (ψ := -106277/500000) 76 50
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t62 : ((1218887269753/10000000000000 : ℚ) : ℝ) ≤ stT76 62 := by
  have hc : ((959753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1218887269753/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((959753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c63 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((596609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2328819/10000000) (δ := 293/50000000) (ψ := -106277/500000) 76 50
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t63 : ((751593349479/10000000000000 : ℚ) : ℝ) ≤ stT76 63 := by
  have hc : ((596559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((751593349479/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((596559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c64 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-529157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5321007/10000000) (δ := 617/100000000) (ψ := -106277/500000) 76 50
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t64 : ((-661509279207/10000000000000 : ℚ) : ℝ) ≤ stT76 64 := by
  have hc : ((-529207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661509279207/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-529207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c65 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-986397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7441161/10000000) (δ := 127/25000000) (ψ := -106277/500000) 76 51
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t65 : ((-305884390889/2500000000000 : ℚ) : ℝ) ≤ stT76 65 := by
  have hc : ((-986447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305884390889/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-986447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c66 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-121443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4540341/10000000) (δ := 91/20000000) (ψ := -106277/500000) 76 51
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t66 : ((-7475839161/250000000000 : ℚ) : ℝ) ≤ stT76 66 := by
  have hc : ((-30367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7475839161/250000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-30367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c67 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((156359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210393/1250000) (δ := 123/20000000) (ψ := -106277/500000) 76 51
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t67 : ((95505317603/1000000000000 : ℚ) : ℝ) ≤ stT76 67 := by
  have hc : ((156349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95505317603/1000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((156349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c68 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((449637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565861/5000000) (δ := 147/20000000) (ψ := -106277/500000) 76 51
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t68 : ((68154322617/625000000000 : ℚ) : ℝ) ≤ stT76 68 := by
  have hc : ((112403/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68154322617/625000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((112403/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c69 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((8599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1952747/5000000) (δ := 147/20000000) (ψ := -106277/500000) 76 51
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t69 : ((5145891021/5000000000000 : ℚ) : ℝ) ≤ stT76 69 := by
  have hc : ((8549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5145891021/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((8549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c70 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-442139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3319677/5000000) (δ := 91/20000000) (ψ := -106277/500000) 76 51
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t70 : ((-132121808889/1250000000000 : ℚ) : ℝ) ≤ stT76 70 := by
  have hc : ((-110541/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132121808889/1250000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-110541/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c71 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-33189/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6373529/10000000) (δ := 559/100000000) (ψ := -106277/500000) 76 52
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t71 : ((-19695240681/200000000000 : ℚ) : ℝ) ≤ stT76 71 := by
  have hc : ((-33191/40000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19695240681/200000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-33191/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c72 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((84239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3716143/10000000) (δ := 161/25000000) (ψ := -106277/500000) 76 52
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t72 : ((99217662579/10000000000000 : ℚ) : ℝ) ≤ stT76 72 := by
  have hc : ((84189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99217662579/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((84189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c73 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((226383/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -273853/2500000) (δ := 121/25000000) (ψ := -106277/500000) 76 52
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t73 : ((529893046551/5000000000000 : ℚ) : ℝ) ≤ stT76 73 := by
  have hc : ((452741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529893046551/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((452741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c74 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((827663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 744831/5000000) (δ := 679/100000000) (ψ := -106277/500000) 76 52
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t74 : ((240520062447/2500000000000 : ℚ) : ℝ) ≤ stT76 74 := by
  have hc : ((827613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240520062447/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((827613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c75 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-45203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1010009/2500000) (δ := 171/25000000) (ψ := -106277/500000) 76 52
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t75 : ((-52253684353/10000000000000 : ℚ) : ℝ) ≤ stT76 75 := by
  have hc : ((-45253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52253684353/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-45253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c76 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-173669/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6556629/10000000) (δ := 121/25000000) (ψ := -106277/500000) 76 52
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t76 : ((-199223533641/2000000000000 : ℚ) : ℝ) ≤ stT76 76 := by
  have hc : ((-173679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-199223533641/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-173679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c77 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-27797/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6667639/10000000) (δ := 633/100000000) (ψ := -106277/500000) 76 53
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t77 : ((-253435268931/2500000000000 : ℚ) : ℝ) ≤ stT76 77 := by
  have hc : ((-444777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253435268931/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-444777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c78 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-115343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -526999/1250000) (δ := 593/100000000) (ψ := -106277/500000) 76 53
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t78 : ((-65328477627/5000000000000 : ℚ) : ℝ) ≤ stT76 78 := by
  have hc : ((-115393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65328477627/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-115393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c79 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((752971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1795577/10000000) (δ := 393/100000000) (ψ := -106277/500000) 76 53
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t79 : ((847101629127/10000000000000 : ℚ) : ℝ) ≤ stT76 79 := by
  have hc : ((752921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((847101629127/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((752921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c80 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((971869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74299/1250000) (δ := 513/100000000) (ψ := -106277/500000) 76 53
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t80 : ((1086525712027/10000000000000 : ℚ) : ℝ) ≤ stT76 80 := by
  have hc : ((971819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1086525712027/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((971819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c81 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((379197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2954671/10000000) (δ := 41/10000000) (ψ := -106277/500000) 76 53
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t81 : ((421274402317/10000000000000 : ℚ) : ℝ) ≤ stT76 81 := by
  have hc : ((379147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421274402317/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((379147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c82 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-517219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1321497/2500000) (δ := 433/100000000) (ψ := -106277/500000) 76 53
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t82 : ((-142807108251/2500000000000 : ℚ) : ℝ) ≤ stT76 82 := by
  have hc : ((-517269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142807108251/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-517269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c83 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-99439/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7589047/10000000) (δ := 713/100000000) (ψ := -106277/500000) 76 53
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t83 : ((-27288502623/250000000000 : ℚ) : ℝ) ≤ stT76 83 := by
  have hc : ((-24861/25000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27288502623/250000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-24861/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c84 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-173419/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73043/125000) (δ := 783/100000000) (ψ := -106277/500000) 76 54
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t84 : ((-37845875067/500000000000 : ℚ) : ℝ) ≤ stT76 84 := by
  have hc : ((-346863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37845875067/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-346863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c85 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((132449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3594893/10000000) (δ := 21/5000000) (ψ := -106277/500000) 76 54
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t85 : ((35901710037/2500000000000 : ℚ) : ℝ) ≤ stT76 85 := by
  have hc : ((132399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35901710037/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((132399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c86 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((106627/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686323/5000000) (δ := 7/1000000) (ψ := -106277/500000) 76 54
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t86 : ((459888133941/5000000000000 : ℚ) : ℝ) ≤ stT76 86 := by
  have hc : ((426483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459888133941/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((426483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c87 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((946183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 823911/10000000) (δ := 623/100000000) (ψ := -106277/500000) 76 54
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t87 : ((63397533931/625000000000 : ℚ) : ℝ) ≤ stT76 87 := by
  have hc : ((946133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63397533931/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((946133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c88 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((182043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2995363/10000000) (δ := 663/100000000) (ψ := -106277/500000) 76 54
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t88 : ((97015867027/2500000000000 : ℚ) : ℝ) ≤ stT76 88 := by
  have hc : ((91009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97015867027/2500000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((91009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c89 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-233597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2571139/5000000) (δ := 1/200000) (ψ := -106277/500000) 76 54
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t89 : ((-61909713189/1250000000000 : ℚ) : ℝ) ≤ stT76 89 := by
  have hc : ((-116811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61909713189/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-116811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c90 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-194479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1453041/2000000) (δ := 1/200000) (ψ := -106277/500000) 76 54
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t90 : ((-205009493477/2000000000000 : ℚ) : ℝ) ≤ stT76 90 := by
  have hc : ((-194489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205009493477/2000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-194489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c91 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-822913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6343289/10000000) (δ := 791/100000000) (ψ := -106277/500000) 76 55
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t91 : ((-172539953691/2000000000000 : ℚ) : ℝ) ≤ stT76 91 := by
  have hc : ((-822963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172539953691/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-822963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c92 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-33873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2133383/5000000) (δ := 551/100000000) (ψ := -106277/500000) 76 55
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t92 : ((-70656214783/5000000000000 : ℚ) : ℝ) ≤ stT76 92 := by
  have hc : ((-67771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70656214783/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-67771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c93 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((63323/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553173/2500000) (δ := 671/100000000) (ψ := -106277/500000) 76 55
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t93 : ((32828831709/500000000000 : ℚ) : ℝ) ≤ stT76 93 := by
  have hc : ((31659/50000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32828831709/500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((31659/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c94 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((62337/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -180587/10000000) (δ := 591/100000000) (ψ := -106277/500000) 76 55
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t94 : ((514339741491/5000000000000 : ℚ) : ℝ) ≤ stT76 94 := by
  have hc : ((498671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514339741491/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((498671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c95 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((148767/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 915007/5000000) (δ := 671/100000000) (ψ := -106277/500000) 76 55
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t95 : ((76310704673/1000000000000 : ℚ) : ℝ) ≤ stT76 95 := by
  have hc : ((148757/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76310704673/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((148757/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c96 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((42959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3819561/10000000) (δ := 671/100000000) (ψ := -106277/500000) 76 55
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t96 : ((2189689179/500000000000 : ℚ) : ℝ) ≤ stT76 96 := by
  have hc : ((42909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2189689179/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((42909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c97 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-338839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5788491/10000000) (δ := 591/100000000) (ψ := -106277/500000) 76 55
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t97 : ((-21504034113/312500000000 : ℚ) : ℝ) ≤ stT76 97 := by
  have hc : ((-21179/31250 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21504034113/312500000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-21179/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c98 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-99891/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3868613/5000000) (δ := 591/100000000) (ψ := -106277/500000) 76 55
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t98 : ((-12613780511/125000000000 : ℚ) : ℝ) ≤ stT76 98 := by
  have hc : ((-12487/12500 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12613780511/125000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-12487/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c99 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-37429/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6041787/10000000) (δ := 401/100000000) (ψ := -106277/500000) 76 56
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t99 : ((-37620079897/500000000000 : ℚ) : ℝ) ≤ stT76 99 := by
  have hc : ((-74863/100000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37620079897/500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-74863/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c100 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-82001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4132223/10000000) (δ := 321/50000000) (ψ := -106277/500000) 76 56
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t100 : ((-82051/10000000 : ℚ) : ℝ) ≤ stT76 100 := by
  have hc : ((-82051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82051/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-82051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c101 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((31211/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112083/500000) (δ := 641/100000000) (ψ := -106277/500000) 76 56
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t101 : ((62107224429/1000000000000 : ℚ) : ℝ) ≤ stT76 101 := by
  have hc : ((62417/100000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62107224429/1000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((62417/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c102 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((247271/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92431/2500000) (δ := 681/100000000) (ψ := -106277/500000) 76 56
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t102 : ((489644523999/5000000000000 : ℚ) : ℝ) ≤ stT76 102 := by
  have hc : ((494517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((489644523999/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((494517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c103 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((51809/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1483949/10000000) (δ := 321/50000000) (ψ := -106277/500000) 76 56
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t103 : ((408366648063/5000000000000 : ℚ) : ℝ) ≤ stT76 103 := by
  have hc : ((414447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408366648063/5000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((414447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c104 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((24053/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103741/312500) (δ := 361/50000000) (ψ := -106277/500000) 76 56
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t104 : ((73690587/3125000000 : ℚ) : ℝ) ≤ stT76 104 := by
  have hc : ((1503/6250 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73690587/3125000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((1503/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c105 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-29103/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284477/2500000) (δ := 401/100000000) (ψ := -106277/500000) 76 56
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t105 : ((-227237571949/5000000000000 : ℚ) : ℝ) ≤ stT76 105 := by
  have hc : ((-232849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227237571949/5000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-232849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c106 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-747/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6938869/10000000) (δ := 341/50000000) (ψ := -106277/500000) 76 56
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t106 : ((-2267467167/25000000000 : ℚ) : ℝ) ≤ stT76 106 := by
  have hc : ((-4669/5000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2267467167/25000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-4669/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c107 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-940201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6985043/10000000) (δ := 511/100000000) (ψ := -106277/500000) 76 57
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t107 : ((-908975430987/10000000000000 : ℚ) : ℝ) ≤ stT76 107 := by
  have hc : ((-940251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-908975430987/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-940251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c108 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-493613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5217589/10000000) (δ := 591/100000000) (ψ := -106277/500000) 76 57
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t108 : ((-475027715413/10000000000000 : ℚ) : ℝ) ≤ stT76 108 := by
  have hc : ((-493663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475027715413/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-493663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c109 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((91593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -433303/1250000) (δ := 153/25000000) (ψ := -106277/500000) 76 57
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t109 : ((2740819099/156250000000 : ℚ) : ℝ) ≤ stT76 109 := by
  have hc : ((5723/31250 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2740819099/156250000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((5723/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c110 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((192413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -432813/2500000) (δ := 123/25000000) (ψ := -106277/500000) 76 57
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t110 : ((183446565531/2500000000000 : ℚ) : ℝ) ≤ stT76 110 := by
  have hc : ((384801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183446565531/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((384801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c111 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((999989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1473/1250000) (δ := 791/100000000) (ψ := -106277/500000) 76 57
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t111 : ((949099101423/10000000000000 : ℚ) : ℝ) ≤ stT76 111 := by
  have hc : ((999939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949099101423/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((999939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c112 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((155903/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 211533/1250000) (δ := 133/25000000) (ψ := -106277/500000) 76 57
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t112 : ((147305010523/2000000000000 : ℚ) : ℝ) ≤ stT76 112 := by
  have hc : ((155893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147305010523/2000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((155893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c113 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((1083/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 845291/2500000) (δ := 631/100000000) (ψ := -106277/500000) 76 57
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t113 : ((50928229/2500000000 : ℚ) : ℝ) ≤ stT76 113 := by
  have hc : ((4331/20000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50928229/2500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((4331/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c114 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-87223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5055183/10000000) (δ := 431/100000000) (ψ := -106277/500000) 76 57
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t114 : ((-40850603269/1000000000000 : ℚ) : ℝ) ≤ stT76 114 := by
  have hc : ((-87233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40850603269/1000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-87233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c115 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-897927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6714583/10000000) (δ := 551/100000000) (ψ := -106277/500000) 76 57
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t115 : ((-167473608477/2000000000000 : ℚ) : ℝ) ≤ stT76 115 := by
  have hc : ((-897977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167473608477/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-897977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c116 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-30613/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7348349/10000000) (δ := 663/100000000) (ψ := -106277/500000) 76 58
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t116 : ((-454798674341/5000000000000 : ℚ) : ℝ) ≤ stT76 116 := by
  have hc : ((-489833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454798674341/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-489833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c117 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-656507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5717437/10000000) (δ := 1/200000) (ψ := -106277/500000) 76 58
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t117 : ((-606987603057/10000000000000 : ℚ) : ℝ) ≤ stT76 117 := by
  have hc : ((-656557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-606987603057/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-656557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c118 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-6931/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2050203/5000000) (δ := 29/5000000) (ψ := -106277/500000) 76 58
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t118 : ((-31925541/5000000000 : ℚ) : ℝ) ≤ stT76 118 := by
  have hc : ((-867/12500 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31925541/5000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-867/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c119 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((108261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2497021/10000000) (δ := 703/100000000) (ψ := -106277/500000) 76 58
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t119 : ((49616737599/1000000000000 : ℚ) : ℝ) ≤ stT76 119 := by
  have hc : ((108251/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49616737599/1000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((108251/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c120 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((934899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -453527/5000000) (δ := 23/5000000) (ψ := -106277/500000) 76 58
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t120 : ((85339560663/1000000000000 : ℚ) : ℝ) ≤ stT76 120 := by
  have hc : ((934849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85339560663/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((934849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c121 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((241083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 669719/10000000) (δ := 21/5000000) (ψ := -106277/500000) 76 58
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t121 : ((43830956169/500000000000 : ℚ) : ℝ) ≤ stT76 121 := by
  have hc : ((482141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43830956169/500000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((482141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c122 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((313381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2233513/10000000) (δ := 23/5000000) (ψ := -106277/500000) 76 58
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t122 : ((70924762023/1250000000000 : ℚ) : ℝ) ≤ stT76 122 := by
  have hc : ((78339/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70924762023/1250000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((78339/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c123 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((56949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1892271/5000000) (δ := 383/100000000) (ψ := -106277/500000) 76 58
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t123 : ((51304064431/10000000000000 : ℚ) : ℝ) ≤ stT76 123 := by
  have hc : ((56899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51304064431/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((56899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c124 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-529837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1330753/2500000) (δ := 463/100000000) (ψ := -106277/500000) 76 58
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t124 : ((-475852832949/10000000000000 : ℚ) : ℝ) ≤ stT76 124 := by
  have hc : ((-529887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475852832949/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-529887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c125 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-920303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54793/80000) (δ := 1/200000) (ψ := -106277/500000) 76 58
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t125 : ((-205797373271/2500000000000 : ℚ) : ℝ) ≤ stT76 125 := by
  have hc : ((-920353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205797373271/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-920353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c126 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-979337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3672443/5000000) (δ := 729/100000000) (ψ := -106277/500000) 76 59
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t126 : ((-872507476077/10000000000000 : ℚ) : ℝ) ≤ stT76 126 := by
  have hc : ((-979387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-872507476077/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-979387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c127 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-693521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2921451/5000000) (δ := 317/50000000) (ψ := -106277/500000) 76 59
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t127 : ((-615445081847/10000000000000 : ℚ) : ℝ) ≤ stT76 127 := by
  have hc : ((-693571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615445081847/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-693571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c128 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-169461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2176349/5000000) (δ := 237/50000000) (ψ := -106277/500000) 76 59
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t128 : ((-37457015181/2500000000000 : ℚ) : ℝ) ≤ stT76 128 := by
  have hc : ((-169511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37457015181/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-169511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c129 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((408819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2874091/10000000) (δ := 729/100000000) (ψ := -106277/500000) 76 59
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t129 : ((7198013321/200000000000 : ℚ) : ℝ) ≤ stT76 129 := by
  have hc : ((408769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7198013321/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((408769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c130 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((169157/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1406903/10000000) (δ := 409/100000000) (ψ := -106277/500000) 76 59
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t130 : ((74175864763/1000000000000 : ℚ) : ℝ) ≤ stT76 130 := by
  have hc : ((169147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74175864763/1000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((169147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c131 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((15622/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49043/10000000) (δ := 609/100000000) (ψ := -106277/500000) 76 59
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t131 : ((54593285227/625000000000 : ℚ) : ℝ) ≤ stT76 131 := by
  have hc : ((499879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54593285227/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((499879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c132 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((826707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493917/10000000) (δ := 609/100000000) (ψ := -106277/500000) 76 59
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t132 : ((179878083229/2500000000000 : ℚ) : ℝ) ≤ stT76 132 := by
  have hc : ((826657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179878083229/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((826657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c133 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((389089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1463943/5000000) (δ := 569/100000000) (ψ := -106277/500000) 76 59
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t133 : ((337339218251/10000000000000 : ℚ) : ℝ) ≤ stT76 133 := by
  have hc : ((389039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337339218251/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((389039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c134 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-168837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2175557/5000000) (δ := 769/100000000) (ψ := -106277/500000) 76 59
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t134 : ((-145896243803/10000000000000 : ℚ) : ℝ) ≤ stT76 134 := by
  have hc : ((-168887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145896243803/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-168887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c135 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-67037/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72047/125000) (δ := 297/50000000) (ψ := -106277/500000) 76 59
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t135 : ((-28850284423/500000000000 : ℚ) : ℝ) ≤ stT76 135 := by
  have hc : ((-33521/50000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28850284423/500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-33521/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c136 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-962371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 358299/500000) (δ := 317/50000000) (ψ := -106277/500000) 76 59
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t136 : ((-825269270553/10000000000000 : ℚ) : ℝ) ≤ stT76 136 := by
  have hc : ((-962421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-825269270553/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-962421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c137 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-480309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1787509/2500000) (δ := 299/50000000) (ψ := -106277/500000) 76 60
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t137 : ((-102594298893/1250000000000 : ℚ) : ℝ) ≤ stT76 137 := by
  have hc : ((-240167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102594298893/1250000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-240167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c138 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-67169/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5768211/10000000) (δ := 129/20000000) (ψ := -106277/500000) 76 60
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t138 : ((-28591168859/500000000000 : ℚ) : ℝ) ≤ stT76 138 := by
  have hc : ((-33587/50000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28591168859/500000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-33587/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c139 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-23331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1099091/2500000) (δ := 259/50000000) (ψ := -106277/500000) 76 60
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t139 : ((-79177594961/5000000000000 : ℚ) : ℝ) ≤ stT76 139 := by
  have hc : ((-93349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79177594961/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-93349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c140 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((349517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3034351/10000000) (δ := 299/50000000) (ψ := -106277/500000) 76 60
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t140 : ((147676716459/5000000000000 : ℚ) : ℝ) ≤ stT76 140 := by
  have hc : ((349467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147676716459/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((349467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c141 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((97759/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105127/625000) (δ := 137/20000000) (ψ := -106277/500000) 76 60
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t141 : ((329290304661/5000000000000 : ℚ) : ℝ) ≤ stT76 141 := by
  have hc : ((391011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329290304661/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((391011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c142 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((495403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339271/10000000) (δ := 81/20000000) (ψ := -106277/500000) 76 60
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t142 : ((207855902709/2500000000000 : ℚ) : ℝ) ≤ stT76 142 := by
  have hc : ((247689/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207855902709/2500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((247689/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c143 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((460991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248517/2500000) (δ := 279/50000000) (ψ := -106277/500000) 76 60
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t143 : ((96369782443/1250000000000 : ℚ) : ℝ) ≤ stT76 143 := by
  have hc : ((230483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96369782443/1250000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((230483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c144 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((600039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 463623/2000000) (δ := 29/4000000) (ψ := -106277/500000) 76 60
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t144 : ((499990633337/10000000000000 : ℚ) : ℝ) ≤ stT76 144 := by
  have hc : ((599989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499990633337/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((599989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c145 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((58663/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3632999/10000000) (δ := 239/50000000) (ψ := -106277/500000) 76 60
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t145 : ((12174040413/1250000000000 : ℚ) : ℝ) ≤ stT76 145 := by
  have hc : ((29319/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12174040413/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((29319/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c146 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-196891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4938847/10000000) (δ := 299/50000000) (ψ := -106277/500000) 76 60
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t146 : ((-20371107887/625000000000 : ℚ) : ℝ) ≤ stT76 146 := by
  have hc : ((-49229/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20371107887/625000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-49229/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c147 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-797727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311789/500000) (δ := 129/20000000) (ψ := -106277/500000) 76 60
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t147 : ((-657996098499/10000000000000 : ℚ) : ℝ) ≤ stT76 147 := by
  have hc : ((-797777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657996098499/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-797777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c148 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-991297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94049/125000) (δ := 21/4000000) (ψ := -106277/500000) 76 60
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t148 : ((-162976455453/2000000000000 : ℚ) : ℝ) ≤ stT76 148 := by
  have hc : ((-991347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162976455453/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-991347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c149 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-928753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6904577/10000000) (δ := 187/25000000) (ψ := -106277/500000) 76 61
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t149 : ((-23778285603/312500000000 : ℚ) : ℝ) ≤ stT76 149 := by
  have hc : ((-928803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23778285603/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-928803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c150 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-157717/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5633669/10000000) (δ := 139/20000000) (ψ := -106277/500000) 76 61
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t150 : ((-257571327123/5000000000000 : ℚ) : ℝ) ≤ stT76 150 := by
  have hc : ((-315459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257571327123/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-315459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c151 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-176753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2185603/5000000) (δ := 127/25000000) (ψ := -106277/500000) 76 61
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t151 : ((-143880336567/10000000000000 : ℚ) : ℝ) ≤ stT76 151 := by
  have hc : ((-176803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143880336567/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-176803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c152 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((318329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -779269/2500000) (δ := 157/25000000) (ψ := -106277/500000) 76 61
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t152 : ((258158324853/10000000000000 : ℚ) : ℝ) ≤ stT76 152 := by
  have hc : ((318279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258158324853/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((318279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c153 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((183183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187117/1000000) (δ := 157/25000000) (ψ := -106277/500000) 76 61
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t153 : ((74042278533/1250000000000 : ℚ) : ℝ) ≤ stT76 153 := by
  have hc : ((366341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74042278533/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((366341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c154 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((484039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31669/500000) (δ := 187/25000000) (ψ := -106277/500000) 76 61
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t154 : ((97507282377/1250000000000 : ℚ) : ℝ) ≤ stT76 154 := by
  have hc : ((242007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97507282377/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((242007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c155 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((6073/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 596397/10000000) (δ := 167/25000000) (ψ := -106277/500000) 76 61
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t155 : ((78043167697/1000000000000 : ℚ) : ℝ) ≤ stT76 155 := by
  have hc : ((97163/100000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78043167697/1000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((97163/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c156 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((93371/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1818267/10000000) (δ := 177/25000000) (ψ := -106277/500000) 76 61
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t156 : ((467197209/7812500000 : ℚ) : ℝ) ≤ stT76 156 := by
  have hc : ((373459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467197209/7812500000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((373459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c157 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((14011/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379041/1250000) (δ := 187/25000000) (ψ := -106277/500000) 76 61
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t157 : ((5590193387/200000000000 : ℚ) : ℝ) ≤ stT76 157 := by
  have hc : ((14009/40000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5590193387/200000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((14009/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c158 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-124353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4238681/10000000) (δ := 137/25000000) (ψ := -106277/500000) 76 61
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t158 : ((-49484900937/5000000000000 : ℚ) : ℝ) ≤ stT76 158 := by
  have hc : ((-124403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49484900937/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-124403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c159 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-284041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 339839/625000) (δ := 187/25000000) (ψ := -106277/500000) 76 61
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t159 : ((-28159888679/625000000000 : ℚ) : ℝ) ≤ stT76 159 := by
  have hc : ((-142033/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28159888679/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-142033/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c160 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-88227/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 132573/200000) (δ := 167/25000000) (ψ := -106277/500000) 76 61
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t160 : ((-871919653/12500000000 : ℚ) : ℝ) ≤ stT76 160 := by
  have hc : ((-11029/12500 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-871919653/12500000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-11029/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c161 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-499931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1562491/2000000) (δ := 99/20000000) (ψ := -106277/500000) 76 61
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t161 : ((-98505205779/1250000000000 : ℚ) : ℝ) ≤ stT76 161 := by
  have hc : ((-124989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98505205779/1250000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-124989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c162 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-898709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3359517/5000000) (δ := 497/100000000) (ψ := -106277/500000) 76 62
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t162 : ((-28245299093/400000000000 : ℚ) : ℝ) ≤ stT76 162 := by
  have hc : ((-898759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28245299093/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-898759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c163 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-604489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27749/50000) (δ := 777/100000000) (ψ := -106277/500000) 76 62
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t163 : ((-473511821679/10000000000000 : ℚ) : ℝ) ≤ stT76 163 := by
  have hc : ((-604539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473511821679/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-604539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c164 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-183249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4387717/10000000) (δ := 577/100000000) (ψ := -106277/500000) 76 62
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t164 : ((-143132506831/10000000000000 : ℚ) : ℝ) ≤ stT76 164 := by
  have hc : ((-183299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143132506831/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-183299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c165 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((274161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616349/5000000) (δ := 273/50000000) (ψ := -106277/500000) 76 62
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t165 : ((106697432639/5000000000000 : ℚ) : ℝ) ≤ stT76 165 := by
  have hc : ((274111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106697432639/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((274111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c166 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((33601/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1042329/5000000) (δ := 333/50000000) (ψ := -106277/500000) 76 62
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t166 : ((1043099031/20000000000 : ℚ) : ℝ) ≤ stT76 166 := by
  have hc : ((67197/100000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1043099031/20000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((67197/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c167 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((116203/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471757/5000000) (δ := 697/100000000) (ψ := -106277/500000) 76 62
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t167 : ((359662870701/5000000000000 : ℚ) : ℝ) ≤ stT76 167 := by
  have hc : ((464787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359662870701/5000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((464787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c168 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((31159/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95409/5000000) (δ := 293/50000000) (ψ := -106277/500000) 76 62
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t168 : ((96153846201/1250000000000 : ℚ) : ℝ) ≤ stT76 168 := by
  have hc : ((498519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96153846201/1250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((498519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c169 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((172827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 659209/5000000) (δ := 657/100000000) (ψ := -106277/500000) 76 62
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t169 : ((13293602091/200000000000 : ℚ) : ℝ) ≤ stT76 169 := by
  have hc : ((172817/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13293602091/200000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((172817/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c170 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((11211/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 487873/2000000) (δ := 497/100000000) (ψ := -106277/500000) 76 62
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t170 : ((214941661/5000000000 : ℚ) : ℝ) ≤ stT76 170 := by
  have hc : ((1121/2000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214941661/5000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((1121/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c171 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((148747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1776869/5000000) (δ := 213/50000000) (ψ := -106277/500000) 76 62
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t171 : ((113711421143/10000000000000 : ℚ) : ℝ) ≤ stT76 171 := by
  have hc : ((148697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113711421143/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((148697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c172 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-144819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1165403/2500000) (δ := 273/50000000) (ψ := -106277/500000) 76 62
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t172 : ((-27610634023/1250000000000 : ℚ) : ℝ) ≤ stT76 172 := by
  have hc : ((-36211/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27610634023/1250000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-36211/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c173 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-167541/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1152613/2000000) (δ := 353/50000000) (ψ := -106277/500000) 76 62
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t173 : ((-127388580301/2500000000000 : ℚ) : ℝ) ≤ stT76 173 := by
  have hc : ((-335107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127388580301/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-335107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c174 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-57607/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6858169/10000000) (δ := 373/50000000) (ψ := -106277/500000) 76 62
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t174 : ((-349393425219/5000000000000 : ℚ) : ℝ) ≤ stT76 174 := by
  have hc : ((-460881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349393425219/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-460881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c175 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-249827/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3880483/5000000) (δ := 557/100000000) (ψ := -106277/500000) 76 63
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t175 : ((-377721846791/5000000000000 : ℚ) : ℝ) ≤ stT76 175 := by
  have hc : ((-499679/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377721846791/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-499679/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c176 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-222863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3339171/5000000) (δ := 717/100000000) (ψ := -106277/500000) 76 63
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t176 : ((-335997743029/5000000000000 : ℚ) : ℝ) ≤ stT76 176 := by
  have hc : ((-445751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335997743029/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-445751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c177 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-310471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1400463/2500000) (δ := 263/50000000) (ψ := -106277/500000) 76 63
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t177 : ((-7293230841/156250000000 : ℚ) : ℝ) ≤ stT76 177 := by
  have hc : ((-9703/15625 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7293230841/156250000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-9703/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c178 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-119713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4531427/10000000) (δ := 203/50000000) (ψ := -106277/500000) 76 63
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t178 : ((-11218432827/625000000000 : ℚ) : ℝ) ≤ stT76 178 := by
  have hc : ((-59869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11218432827/625000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-59869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c179 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((182961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1733499/5000000) (δ := 363/50000000) (ψ := -106277/500000) 76 63
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t179 : ((27342816657/2000000000000 : ℚ) : ℝ) ≤ stT76 179 := by
  have hc : ((182911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27342816657/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((182911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c180 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((570731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4817/20000) (δ := 203/50000000) (ψ := -106277/500000) 76 63
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t180 : ((85071987351/2000000000000 : ℚ) : ℝ) ≤ stT76 180 := by
  have hc : ((570681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85071987351/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((570681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c181 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((1713/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -271173/2000000) (δ := 263/50000000) (ψ := -106277/500000) 76 63
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t181 : ((6365941463/100000000000 : ℚ) : ℝ) ≤ stT76 181 := by
  have hc : ((17129/20000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6365941463/100000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((17129/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c182 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((99237/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -309031/10000000) (δ := 637/100000000) (ψ := -106277/500000) 76 63
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t182 : ((2298613149/31250000000 : ℚ) : ℝ) ≤ stT76 182 := by
  have hc : ((3101/3125 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2298613149/31250000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((3101/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c183 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((119679/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183017/2500000) (δ := 397/100000000) (ψ := -106277/500000) 76 63
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t183 : ((353858439711/5000000000000 : ℚ) : ℝ) ≤ stT76 183 := by
  have hc : ((478691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353858439711/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((478691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c184 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((190079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1767493/10000000) (δ := 437/100000000) (ψ := -106277/500000) 76 63
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t184 : ((280237468797/5000000000000 : ℚ) : ℝ) ≤ stT76 184 := by
  have hc : ((380133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280237468797/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((380133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c185 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((436653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559461/2000000) (δ := 303/50000000) (ψ := -106277/500000) 76 63
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t185 : ((160498319021/5000000000000 : ℚ) : ℝ) ≤ stT76 185 := by
  have hc : ((436603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160498319021/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((436603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c186 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((42157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3821567/10000000) (δ := 557/100000000) (ψ := -106277/500000) 76 63
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t186 : ((6174865229/2000000000000 : ℚ) : ℝ) ≤ stT76 186 := by
  have hc : ((42107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6174865229/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((42107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c187 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-71453/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 302521/625000) (δ := 323/50000000) (ψ := -106277/500000) 76 63
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t187 : ((-52258962399/2000000000000 : ℚ) : ℝ) ≤ stT76 187 := by
  have hc : ((-71463/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52258962399/2000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-71463/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c188 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-348309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 731709/1250000) (δ := 477/100000000) (ψ := -106277/500000) 76 63
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t188 : ((-5080973891/100000000000 : ℚ) : ℝ) ≤ stT76 188 := by
  have hc : ((-174167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5080973891/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-174167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c189 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-115281/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6861631/10000000) (δ := 343/50000000) (ψ := -106277/500000) 76 63
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t189 : ((-335436554557/5000000000000 : ℚ) : ℝ) ≤ stT76 189 := by
  have hc : ((-461149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335436554557/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-461149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c190 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7843691/10000000) (δ := 527/100000000) (ψ := -106277/500000) 76 64
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t190 : ((-362753735017/5000000000000 : ℚ) : ℝ) ≤ stT76 190 := by
  have hc : ((-500021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362753735017/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-500021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c191 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-459931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6846313/10000000) (δ := 139/25000000) (ψ := -106277/500000) 76 64
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t191 : ((-3328126627/50000000000 : ℚ) : ℝ) ≤ stT76 191 := by
  have hc : ((-114989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3328126627/50000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-114989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c192 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-696753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91471/156250) (δ := 527/100000000) (ψ := -106277/500000) 76 64
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t192 : ((-62859295433/1250000000000 : ℚ) : ℝ) ≤ stT76 192 := by
  have hc : ((-696803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62859295433/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-696803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c193 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((-183627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4867129/10000000) (δ := 647/100000000) (ψ := -106277/500000) 76 64
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t193 : ((-4131114001/156250000000 : ℚ) : ℝ) ≤ stT76 193 := by
  have hc : ((-45913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4131114001/156250000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-45913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c194 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((1671/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1942607/5000000) (δ := 447/100000000) (ψ := -106277/500000) 76 64
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t194 : ((299029507/250000000000 : ℚ) : ℝ) ≤ stT76 194 := by
  have hc : ((833/50000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299029507/250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((833/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c195 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((99069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2908349/10000000) (δ := 407/100000000) (ψ := -106277/500000) 76 64
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t195 : ((70935746441/2500000000000 : ℚ) : ℝ) ≤ stT76 195 := by
  have hc : ((198113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70935746441/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((198113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c196 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((714707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936479/10000000) (δ := 447/100000000) (ψ := -106277/500000) 76 64
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t196 : ((102093755049/2000000000000 : ℚ) : ℝ) ≤ stT76 196 := by
  have hc : ((714657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102093755049/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((714657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c197 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((185147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242389/2500000) (δ := 139/25000000) (ψ := -106277/500000) 76 64
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t197 : ((13190455839/200000000000 : ℚ) : ℝ) ≤ stT76 197 := by
  have hc : ((185137/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13190455839/200000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((185137/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c198 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((199999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7529/10000000) (δ := 139/25000000) (ψ := -106277/500000) 76 64
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t198 : ((142125982641/2000000000000 : ℚ) : ℝ) ≤ stT76 198 := by
  have hc : ((199989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142125982641/2000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((199989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c199 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((232179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237413/2500000) (δ := 149/25000000) (ψ := -106277/500000) 76 64
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t199 : ((329156841373/5000000000000 : ℚ) : ℝ) ≤ stT76 199 := by
  have hc : ((464333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329156841373/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((464333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_c200 :
    |Real.cos (((76 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((28971/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 380407/2000000) (δ := 487/100000000) (ψ := -106277/500000) 76 64
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st76_t200 : ((10242076857/200000000000 : ℚ) : ℝ) ≤ stT76 200 := by
  have hc : ((28969/40000 : ℚ) : ℝ)
      ≤ Real.cos (((76 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-106277/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st76_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10242076857/200000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((28969/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st76_p1 : ((195489/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT76 (i+1) := by
  rw [Finset.sum_range_one]
  exact st76_t1

theorem st76_p2 : ((905342315241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT76 (i+1))
      = (∑ i ∈ Finset.range 1, stT76 (i+1)) + stT76 2 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 1
    simpa using h
  have hprev := st76_p1
  have hstep := st76_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p3 : ((1084451628243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT76 (i+1))
      = (∑ i ∈ Finset.range 2, stT76 (i+1)) + stT76 3 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 2
    simpa using h
  have hprev := st76_p2
  have hstep := st76_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p4 : ((2692926628243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT76 (i+1))
      = (∑ i ∈ Finset.range 3, stT76 (i+1)) + stT76 4 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 3
    simpa using h
  have hprev := st76_p3
  have hstep := st76_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p5 : ((-1779298814477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT76 (i+1))
      = (∑ i ∈ Finset.range 4, stT76 (i+1)) + stT76 5 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 4
    simpa using h
  have hprev := st76_p4
  have hstep := st76_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p6 : ((-2880254664951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT76 (i+1))
      = (∑ i ∈ Finset.range 5, stT76 (i+1)) + stT76 6 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 5
    simpa using h
  have hprev := st76_p5
  have hstep := st76_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p7 : ((-6288942626781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT76 (i+1))
      = (∑ i ∈ Finset.range 6, stT76 (i+1)) + stT76 7 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 6
    simpa using h
  have hprev := st76_p6
  have hstep := st76_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p8 : ((-1227820825617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT76 (i+1))
      = (∑ i ∈ Finset.range 7, stT76 (i+1)) + stT76 8 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 7
    simpa using h
  have hprev := st76_p7
  have hstep := st76_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p9 : ((-933362976699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT76 (i+1))
      = (∑ i ∈ Finset.range 8, stT76 (i+1)) + stT76 9 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 8
    simpa using h
  have hprev := st76_p8
  have hstep := st76_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p10 : ((-5089994117927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT76 (i+1))
      = (∑ i ∈ Finset.range 9, stT76 (i+1)) + stT76 10 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 9
    simpa using h
  have hprev := st76_p9
  have hstep := st76_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p11 : ((-540402710843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT76 (i+1))
      = (∑ i ∈ Finset.range 10, stT76 (i+1)) + stT76 11 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 10
    simpa using h
  have hprev := st76_p10
  have hstep := st76_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p12 : ((268759257283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT76 (i+1))
      = (∑ i ∈ Finset.range 11, stT76 (i+1)) + stT76 12 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 11
    simpa using h
  have hprev := st76_p11
  have hstep := st76_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p13 : ((2854471119283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT76 (i+1))
      = (∑ i ∈ Finset.range 12, stT76 (i+1)) + stT76 13 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 12
    simpa using h
  have hprev := st76_p12
  have hstep := st76_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p14 : ((5422110937759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT76 (i+1))
      = (∑ i ∈ Finset.range 13, stT76 (i+1)) + stT76 14 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 13
    simpa using h
  have hprev := st76_p13
  have hstep := st76_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p15 : ((6060902514923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT76 (i+1))
      = (∑ i ∈ Finset.range 14, stT76 (i+1)) + stT76 15 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 14
    simpa using h
  have hprev := st76_p14
  have hstep := st76_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p16 : ((3801661611227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT76 (i+1))
      = (∑ i ∈ Finset.range 15, stT76 (i+1)) + stT76 16 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 15
    simpa using h
  have hprev := st76_p15
  have hstep := st76_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p17 : ((299804139749/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT76 (i+1))
      = (∑ i ∈ Finset.range 16, stT76 (i+1)) + stT76 17 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 16
    simpa using h
  have hprev := st76_p16
  have hstep := st76_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p18 : ((1338458847257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT76 (i+1))
      = (∑ i ∈ Finset.range 17, stT76 (i+1)) + stT76 18 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 17
    simpa using h
  have hprev := st76_p17
  have hstep := st76_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p19 : ((1997400712783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT76 (i+1))
      = (∑ i ∈ Finset.range 18, stT76 (i+1)) + stT76 19 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 18
    simpa using h
  have hprev := st76_p18
  have hstep := st76_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p20 : ((1860462790429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT76 (i+1))
      = (∑ i ∈ Finset.range 19, stT76 (i+1)) + stT76 20 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 19
    simpa using h
  have hprev := st76_p19
  have hstep := st76_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p21 : ((255425246177/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT76 (i+1))
      = (∑ i ∈ Finset.range 20, stT76 (i+1)) + stT76 21 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 20
    simpa using h
  have hprev := st76_p20
  have hstep := st76_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p22 : ((806230689929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT76 (i+1))
      = (∑ i ∈ Finset.range 21, stT76 (i+1)) + stT76 22 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 21
    simpa using h
  have hprev := st76_p21
  have hstep := st76_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p23 : ((1311165511967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT76 (i+1))
      = (∑ i ∈ Finset.range 22, stT76 (i+1)) + stT76 23 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 22
    simpa using h
  have hprev := st76_p22
  have hstep := st76_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p24 : ((807184903409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT76 (i+1))
      = (∑ i ∈ Finset.range 23, stT76 (i+1)) + stT76 24 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 23
    simpa using h
  have hprev := st76_p23
  have hstep := st76_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p25 : ((1297478403409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT76 (i+1))
      = (∑ i ∈ Finset.range 24, stT76 (i+1)) + stT76 25 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 24
    simpa using h
  have hprev := st76_p24
  have hstep := st76_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p26 : ((209559009903/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT76 (i+1))
      = (∑ i ∈ Finset.range 25, stT76 (i+1)) + stT76 26 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 25
    simpa using h
  have hprev := st76_p25
  have hstep := st76_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p27 : ((76663591257/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT76 (i+1))
      = (∑ i ∈ Finset.range 26, stT76 (i+1)) + stT76 27 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 26
    simpa using h
  have hprev := st76_p26
  have hstep := st76_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p28 : ((3899506002243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT76 (i+1))
      = (∑ i ∈ Finset.range 27, stT76 (i+1)) + stT76 28 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 27
    simpa using h
  have hprev := st76_p27
  have hstep := st76_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p29 : ((2030600092359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT76 (i+1))
      = (∑ i ∈ Finset.range 28, stT76 (i+1)) + stT76 29 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 28
    simpa using h
  have hprev := st76_p28
  have hstep := st76_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p30 : ((4900695979669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT76 (i+1))
      = (∑ i ∈ Finset.range 29, stT76 (i+1)) + stT76 30 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 29
    simpa using h
  have hprev := st76_p29
  have hstep := st76_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p31 : ((3278227006661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT76 (i+1))
      = (∑ i ∈ Finset.range 30, stT76 (i+1)) + stT76 31 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 30
    simpa using h
  have hprev := st76_p30
  have hstep := st76_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p32 : ((4974446213343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT76 (i+1))
      = (∑ i ∈ Finset.range 31, stT76 (i+1)) + stT76 32 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 31
    simpa using h
  have hprev := st76_p31
  have hstep := st76_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p33 : ((416657075619/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT76 (i+1))
      = (∑ i ∈ Finset.range 32, stT76 (i+1)) + stT76 33 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 32
    simpa using h
  have hprev := st76_p32
  have hstep := st76_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p34 : ((70282429647/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT76 (i+1))
      = (∑ i ∈ Finset.range 33, stT76 (i+1)) + stT76 34 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 33
    simpa using h
  have hprev := st76_p33
  have hstep := st76_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p35 : ((2577537089529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT76 (i+1))
      = (∑ i ∈ Finset.range 34, stT76 (i+1)) + stT76 35 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 34
    simpa using h
  have hprev := st76_p34
  have hstep := st76_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p36 : ((1972643635217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT76 (i+1))
      = (∑ i ∈ Finset.range 35, stT76 (i+1)) + stT76 36 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 35
    simpa using h
  have hprev := st76_p35
  have hstep := st76_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p37 : ((221449293019/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT76 (i+1))
      = (∑ i ∈ Finset.range 36, stT76 (i+1)) + stT76 37 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 36
    simpa using h
  have hprev := st76_p36
  have hstep := st76_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p38 : ((80156850361/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT76 (i+1))
      = (∑ i ∈ Finset.range 37, stT76 (i+1)) + stT76 38 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 37
    simpa using h
  have hprev := st76_p37
  have hstep := st76_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p39 : ((52620429247/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT76 (i+1))
      = (∑ i ∈ Finset.range 38, stT76 (i+1)) + stT76 39 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 38
    simpa using h
  have hprev := st76_p38
  have hstep := st76_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p40 : ((413758430207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT76 (i+1))
      = (∑ i ∈ Finset.range 39, stT76 (i+1)) + stT76 40 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 39
    simpa using h
  have hprev := st76_p39
  have hstep := st76_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p41 : ((4802293089523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT76 (i+1))
      = (∑ i ∈ Finset.range 40, stT76 (i+1)) + stT76 41 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 40
    simpa using h
  have hprev := st76_p40
  have hstep := st76_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p42 : ((2430950998673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT76 (i+1))
      = (∑ i ∈ Finset.range 41, stT76 (i+1)) + stT76 42 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 41
    simpa using h
  have hprev := st76_p41
  have hstep := st76_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p43 : ((1680580112387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT76 (i+1))
      = (∑ i ∈ Finset.range 42, stT76 (i+1)) + stT76 43 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 42
    simpa using h
  have hprev := st76_p42
  have hstep := st76_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p44 : ((1942716964779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT76 (i+1))
      = (∑ i ∈ Finset.range 43, stT76 (i+1)) + stT76 44 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 43
    simpa using h
  have hprev := st76_p43
  have hstep := st76_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p45 : ((5198990325029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT76 (i+1))
      = (∑ i ∈ Finset.range 44, stT76 (i+1)) + stT76 45 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 44
    simpa using h
  have hprev := st76_p44
  have hstep := st76_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p46 : ((4376182871929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT76 (i+1))
      = (∑ i ∈ Finset.range 45, stT76 (i+1)) + stT76 46 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 45
    simpa using h
  have hprev := st76_p45
  have hstep := st76_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p47 : ((3219912475579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT76 (i+1))
      = (∑ i ∈ Finset.range 46, stT76 (i+1)) + stT76 47 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 46
    simpa using h
  have hprev := st76_p46
  have hstep := st76_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p48 : ((1033233080551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT76 (i+1))
      = (∑ i ∈ Finset.range 47, stT76 (i+1)) + stT76 48 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 47
    simpa using h
  have hprev := st76_p47
  have hstep := st76_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p49 : ((52426119893/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT76 (i+1))
      = (∑ i ∈ Finset.range 48, stT76 (i+1)) + stT76 49 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 48
    simpa using h
  have hprev := st76_p48
  have hstep := st76_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p50 : ((439141779591/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT76 (i+1))
      = (∑ i ∈ Finset.range 49, stT76 (i+1)) + stT76 50 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 49
    simpa using h
  have hprev := st76_p49
  have hstep := st76_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p51 : ((3220064535757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT76 (i+1))
      = (∑ i ∈ Finset.range 50, stT76 (i+1)) + stT76 51 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 50
    simpa using h
  have hprev := st76_p50
  have hstep := st76_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p52 : ((3866482794007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT76 (i+1))
      = (∑ i ∈ Finset.range 51, stT76 (i+1)) + stT76 52 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 51
    simpa using h
  have hprev := st76_p51
  have hstep := st76_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p53 : ((2575535660991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT76 (i+1))
      = (∑ i ∈ Finset.range 52, stT76 (i+1)) + stT76 53 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 52
    simpa using h
  have hprev := st76_p52
  have hstep := st76_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p54 : ((2432565030069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT76 (i+1))
      = (∑ i ∈ Finset.range 53, stT76 (i+1)) + stT76 54 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 53
    simpa using h
  have hprev := st76_p53
  have hstep := st76_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p55 : ((1758753369269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT76 (i+1))
      = (∑ i ∈ Finset.range 54, stT76 (i+1)) + stT76 55 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 54
    simpa using h
  have hprev := st76_p54
  have hstep := st76_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p56 : ((824157138627/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT76 (i+1))
      = (∑ i ∈ Finset.range 55, stT76 (i+1)) + stT76 56 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 55
    simpa using h
  have hprev := st76_p55
  have hstep := st76_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p57 : ((1130202840281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT76 (i+1))
      = (∑ i ∈ Finset.range 56, stT76 (i+1)) + stT76 57 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 56
    simpa using h
  have hprev := st76_p56
  have hstep := st76_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p58 : ((1326397580501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT76 (i+1))
      = (∑ i ∈ Finset.range 57, stT76 (i+1)) + stT76 58 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 57
    simpa using h
  have hprev := st76_p57
  have hstep := st76_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p59 : ((1127208410501/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT76 (i+1))
      = (∑ i ∈ Finset.range 58, stT76 (i+1)) + stT76 59 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 58
    simpa using h
  have hprev := st76_p58
  have hstep := st76_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p60 : ((1651425331377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT76 (i+1))
      = (∑ i ∈ Finset.range 59, stT76 (i+1)) + stT76 60 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 59
    simpa using h
  have hprev := st76_p59
  have hstep := st76_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p61 : ((336741577989/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT76 (i+1))
      = (∑ i ∈ Finset.range 60, stT76 (i+1)) + stT76 61 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 60
    simpa using h
  have hprev := st76_p60
  have hstep := st76_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p62 : ((4586303049643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT76 (i+1))
      = (∑ i ∈ Finset.range 61, stT76 (i+1)) + stT76 62 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 61
    simpa using h
  have hprev := st76_p61
  have hstep := st76_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p63 : ((2668948199561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT76 (i+1))
      = (∑ i ∈ Finset.range 62, stT76 (i+1)) + stT76 63 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 62
    simpa using h
  have hprev := st76_p62
  have hstep := st76_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p64 : ((935277423983/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT76 (i+1))
      = (∑ i ∈ Finset.range 63, stT76 (i+1)) + stT76 64 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 63
    simpa using h
  have hprev := st76_p63
  have hstep := st76_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p65 : ((3452849556359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT76 (i+1))
      = (∑ i ∈ Finset.range 64, stT76 (i+1)) + stT76 65 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 64
    simpa using h
  have hprev := st76_p64
  have hstep := st76_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p66 : ((3153815989919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT76 (i+1))
      = (∑ i ∈ Finset.range 65, stT76 (i+1)) + stT76 66 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 65
    simpa using h
  have hprev := st76_p65
  have hstep := st76_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p67 : ((4108869165949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT76 (i+1))
      = (∑ i ∈ Finset.range 66, stT76 (i+1)) + stT76 67 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 66
    simpa using h
  have hprev := st76_p66
  have hstep := st76_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p68 : ((5199338327821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT76 (i+1))
      = (∑ i ∈ Finset.range 67, stT76 (i+1)) + stT76 68 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 67
    simpa using h
  have hprev := st76_p67
  have hstep := st76_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p69 : ((5209630109863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT76 (i+1))
      = (∑ i ∈ Finset.range 68, stT76 (i+1)) + stT76 69 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 68
    simpa using h
  have hprev := st76_p68
  have hstep := st76_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p70 : ((4152655638751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT76 (i+1))
      = (∑ i ∈ Finset.range 69, stT76 (i+1)) + stT76 70 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 69
    simpa using h
  have hprev := st76_p69
  have hstep := st76_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p71 : ((3167893604701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT76 (i+1))
      = (∑ i ∈ Finset.range 70, stT76 (i+1)) + stT76 71 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 70
    simpa using h
  have hprev := st76_p70
  have hstep := st76_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p72 : ((40838890841/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT76 (i+1))
      = (∑ i ∈ Finset.range 71, stT76 (i+1)) + stT76 72 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 71
    simpa using h
  have hprev := st76_p71
  have hstep := st76_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p73 : ((2163448680191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT76 (i+1))
      = (∑ i ∈ Finset.range 72, stT76 (i+1)) + stT76 73 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 72
    simpa using h
  have hprev := st76_p72
  have hstep := st76_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p74 : ((528897761017/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT76 (i+1))
      = (∑ i ∈ Finset.range 73, stT76 (i+1)) + stT76 74 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 73
    simpa using h
  have hprev := st76_p73
  have hstep := st76_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p75 : ((5236723925817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT76 (i+1))
      = (∑ i ∈ Finset.range 74, stT76 (i+1)) + stT76 75 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 74
    simpa using h
  have hprev := st76_p74
  have hstep := st76_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p76 : ((1060151564403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT76 (i+1))
      = (∑ i ∈ Finset.range 75, stT76 (i+1)) + stT76 76 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 75
    simpa using h
  have hprev := st76_p75
  have hstep := st76_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p77 : ((50419768467/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT76 (i+1))
      = (∑ i ∈ Finset.range 76, stT76 (i+1)) + stT76 77 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 76
    simpa using h
  have hprev := st76_p76
  have hstep := st76_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p78 : ((1548104113317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT76 (i+1))
      = (∑ i ∈ Finset.range 77, stT76 (i+1)) + stT76 78 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 77
    simpa using h
  have hprev := st76_p77
  have hstep := st76_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p79 : ((3943309855761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT76 (i+1))
      = (∑ i ∈ Finset.range 78, stT76 (i+1)) + stT76 79 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 78
    simpa using h
  have hprev := st76_p78
  have hstep := st76_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p80 : ((1257458891947/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT76 (i+1))
      = (∑ i ∈ Finset.range 79, stT76 (i+1)) + stT76 80 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 79
    simpa using h
  have hprev := st76_p79
  have hstep := st76_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p81 : ((1090221994021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT76 (i+1))
      = (∑ i ∈ Finset.range 80, stT76 (i+1)) + stT76 81 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 80
    simpa using h
  have hprev := st76_p80
  have hstep := st76_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p82 : ((4879881537101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT76 (i+1))
      = (∑ i ∈ Finset.range 81, stT76 (i+1)) + stT76 82 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 81
    simpa using h
  have hprev := st76_p81
  have hstep := st76_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p83 : ((3788341432181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT76 (i+1))
      = (∑ i ∈ Finset.range 82, stT76 (i+1)) + stT76 83 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 82
    simpa using h
  have hprev := st76_p82
  have hstep := st76_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p84 : ((3031423930841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT76 (i+1))
      = (∑ i ∈ Finset.range 83, stT76 (i+1)) + stT76 84 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 83
    simpa using h
  have hprev := st76_p83
  have hstep := st76_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p85 : ((3175030770989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT76 (i+1))
      = (∑ i ∈ Finset.range 84, stT76 (i+1)) + stT76 85 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 84
    simpa using h
  have hprev := st76_p84
  have hstep := st76_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p86 : ((4094807038871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT76 (i+1))
      = (∑ i ∈ Finset.range 85, stT76 (i+1)) + stT76 86 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 85
    simpa using h
  have hprev := st76_p85
  have hstep := st76_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p87 : ((5109167581767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT76 (i+1))
      = (∑ i ∈ Finset.range 86, stT76 (i+1)) + stT76 87 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 86
    simpa using h
  have hprev := st76_p86
  have hstep := st76_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p88 : ((43977848399/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT76 (i+1))
      = (∑ i ∈ Finset.range 87, stT76 (i+1)) + stT76 88 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 87
    simpa using h
  have hprev := st76_p87
  have hstep := st76_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p89 : ((5001953344363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT76 (i+1))
      = (∑ i ∈ Finset.range 88, stT76 (i+1)) + stT76 89 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 88
    simpa using h
  have hprev := st76_p88
  have hstep := st76_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p90 : ((1988452938489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT76 (i+1))
      = (∑ i ∈ Finset.range 89, stT76 (i+1)) + stT76 90 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 89
    simpa using h
  have hprev := st76_p89
  have hstep := st76_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p91 : ((3114206108523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT76 (i+1))
      = (∑ i ∈ Finset.range 90, stT76 (i+1)) + stT76 91 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 90
    simpa using h
  have hprev := st76_p90
  have hstep := st76_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p92 : ((2972893678957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT76 (i+1))
      = (∑ i ∈ Finset.range 91, stT76 (i+1)) + stT76 92 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 91
    simpa using h
  have hprev := st76_p91
  have hstep := st76_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p93 : ((3629470313137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT76 (i+1))
      = (∑ i ∈ Finset.range 92, stT76 (i+1)) + stT76 93 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 92
    simpa using h
  have hprev := st76_p92
  have hstep := st76_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p94 : ((4658149796119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT76 (i+1))
      = (∑ i ∈ Finset.range 93, stT76 (i+1)) + stT76 94 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 93
    simpa using h
  have hprev := st76_p93
  have hstep := st76_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p95 : ((5421256842849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT76 (i+1))
      = (∑ i ∈ Finset.range 94, stT76 (i+1)) + stT76 95 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 94
    simpa using h
  have hprev := st76_p94
  have hstep := st76_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p96 : ((5465050626429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT76 (i+1))
      = (∑ i ∈ Finset.range 95, stT76 (i+1)) + stT76 96 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 95
    simpa using h
  have hprev := st76_p95
  have hstep := st76_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p97 : ((4776921534813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT76 (i+1))
      = (∑ i ∈ Finset.range 96, stT76 (i+1)) + stT76 97 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 96
    simpa using h
  have hprev := st76_p96
  have hstep := st76_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p98 : ((3767819093933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT76 (i+1))
      = (∑ i ∈ Finset.range 97, stT76 (i+1)) + stT76 98 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 97
    simpa using h
  have hprev := st76_p97
  have hstep := st76_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p99 : ((3015417495993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT76 (i+1))
      = (∑ i ∈ Finset.range 98, stT76 (i+1)) + stT76 99 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 98
    simpa using h
  have hprev := st76_p98
  have hstep := st76_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p100 : ((2933366495993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT76 (i+1))
      = (∑ i ∈ Finset.range 99, stT76 (i+1)) + stT76 100 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 99
    simpa using h
  have hprev := st76_p99
  have hstep := st76_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p101 : ((3554438740283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT76 (i+1))
      = (∑ i ∈ Finset.range 100, stT76 (i+1)) + stT76 101 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 100
    simpa using h
  have hprev := st76_p100
  have hstep := st76_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p102 : ((4533727788281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT76 (i+1))
      = (∑ i ∈ Finset.range 101, stT76 (i+1)) + stT76 102 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 101
    simpa using h
  have hprev := st76_p101
  have hstep := st76_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p103 : ((5350461084407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT76 (i+1))
      = (∑ i ∈ Finset.range 102, stT76 (i+1)) + stT76 103 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 102
    simpa using h
  have hprev := st76_p102
  have hstep := st76_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p104 : ((5586270962807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT76 (i+1))
      = (∑ i ∈ Finset.range 103, stT76 (i+1)) + stT76 104 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 103
    simpa using h
  have hprev := st76_p103
  have hstep := st76_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p105 : ((5131795818909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT76 (i+1))
      = (∑ i ∈ Finset.range 104, stT76 (i+1)) + stT76 105 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 104
    simpa using h
  have hprev := st76_p104
  have hstep := st76_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p106 : ((4224808952109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT76 (i+1))
      = (∑ i ∈ Finset.range 105, stT76 (i+1)) + stT76 106 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 105
    simpa using h
  have hprev := st76_p105
  have hstep := st76_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p107 : ((1657916760561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT76 (i+1))
      = (∑ i ∈ Finset.range 106, stT76 (i+1)) + stT76 107 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 106
    simpa using h
  have hprev := st76_p106
  have hstep := st76_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p108 : ((2840805805709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT76 (i+1))
      = (∑ i ∈ Finset.range 107, stT76 (i+1)) + stT76 108 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 107
    simpa using h
  have hprev := st76_p107
  have hstep := st76_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p109 : ((603243645609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT76 (i+1))
      = (∑ i ∈ Finset.range 108, stT76 (i+1)) + stT76 109 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 108
    simpa using h
  have hprev := st76_p108
  have hstep := st76_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p110 : ((3750004490169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT76 (i+1))
      = (∑ i ∈ Finset.range 109, stT76 (i+1)) + stT76 110 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 109
    simpa using h
  have hprev := st76_p109
  have hstep := st76_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p111 : ((587387948949/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT76 (i+1))
      = (∑ i ∈ Finset.range 110, stT76 (i+1)) + stT76 111 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 110
    simpa using h
  have hprev := st76_p110
  have hstep := st76_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p112 : ((5435628644207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT76 (i+1))
      = (∑ i ∈ Finset.range 111, stT76 (i+1)) + stT76 112 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 111
    simpa using h
  have hprev := st76_p111
  have hstep := st76_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p113 : ((5639341560207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT76 (i+1))
      = (∑ i ∈ Finset.range 112, stT76 (i+1)) + stT76 113 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 112
    simpa using h
  have hprev := st76_p112
  have hstep := st76_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p114 : ((5230835527517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT76 (i+1))
      = (∑ i ∈ Finset.range 113, stT76 (i+1)) + stT76 114 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 113
    simpa using h
  have hprev := st76_p113
  have hstep := st76_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p115 : ((1098366871283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT76 (i+1))
      = (∑ i ∈ Finset.range 114, stT76 (i+1)) + stT76 115 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 114
    simpa using h
  have hprev := st76_p114
  have hstep := st76_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p116 : ((69677402729/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT76 (i+1))
      = (∑ i ∈ Finset.range 115, stT76 (i+1)) + stT76 116 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 115
    simpa using h
  have hprev := st76_p115
  have hstep := st76_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p117 : ((2876882533393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT76 (i+1))
      = (∑ i ∈ Finset.range 116, stT76 (i+1)) + stT76 117 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 116
    simpa using h
  have hprev := st76_p116
  have hstep := st76_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p118 : ((2813031451393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT76 (i+1))
      = (∑ i ∈ Finset.range 117, stT76 (i+1)) + stT76 118 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 117
    simpa using h
  have hprev := st76_p117
  have hstep := st76_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p119 : ((3309198827383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT76 (i+1))
      = (∑ i ∈ Finset.range 118, stT76 (i+1)) + stT76 119 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 118
    simpa using h
  have hprev := st76_p118
  have hstep := st76_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p120 : ((4162594434013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT76 (i+1))
      = (∑ i ∈ Finset.range 119, stT76 (i+1)) + stT76 120 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 119
    simpa using h
  have hprev := st76_p119
  have hstep := st76_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p121 : ((5039213557393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT76 (i+1))
      = (∑ i ∈ Finset.range 120, stT76 (i+1)) + stT76 121 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 120
    simpa using h
  have hprev := st76_p120
  have hstep := st76_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p122 : ((5606611653577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT76 (i+1))
      = (∑ i ∈ Finset.range 121, stT76 (i+1)) + stT76 122 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 121
    simpa using h
  have hprev := st76_p121
  have hstep := st76_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p123 : ((707239464751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT76 (i+1))
      = (∑ i ∈ Finset.range 122, stT76 (i+1)) + stT76 123 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 122
    simpa using h
  have hprev := st76_p122
  have hstep := st76_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p124 : ((5182062885059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT76 (i+1))
      = (∑ i ∈ Finset.range 123, stT76 (i+1)) + stT76 124 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 123
    simpa using h
  have hprev := st76_p123
  have hstep := st76_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p125 : ((174354935679/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT76 (i+1))
      = (∑ i ∈ Finset.range 124, stT76 (i+1)) + stT76 125 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 124
    simpa using h
  have hprev := st76_p124
  have hstep := st76_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p126 : ((1743182957949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT76 (i+1))
      = (∑ i ∈ Finset.range 125, stT76 (i+1)) + stT76 126 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 125
    simpa using h
  have hprev := st76_p125
  have hstep := st76_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p127 : ((2870920834051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT76 (i+1))
      = (∑ i ∈ Finset.range 126, stT76 (i+1)) + stT76 127 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 126
    simpa using h
  have hprev := st76_p126
  have hstep := st76_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p128 : ((2721092773327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT76 (i+1))
      = (∑ i ∈ Finset.range 127, stT76 (i+1)) + stT76 128 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 127
    simpa using h
  have hprev := st76_p127
  have hstep := st76_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p129 : ((3080993439377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT76 (i+1))
      = (∑ i ∈ Finset.range 128, stT76 (i+1)) + stT76 129 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 128
    simpa using h
  have hprev := st76_p128
  have hstep := st76_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p130 : ((3822752087007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT76 (i+1))
      = (∑ i ∈ Finset.range 129, stT76 (i+1)) + stT76 130 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 129
    simpa using h
  have hprev := st76_p129
  have hstep := st76_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p131 : ((4696244650639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT76 (i+1))
      = (∑ i ∈ Finset.range 130, stT76 (i+1)) + stT76 131 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 130
    simpa using h
  have hprev := st76_p130
  have hstep := st76_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p132 : ((1083151396711/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT76 (i+1))
      = (∑ i ∈ Finset.range 131, stT76 (i+1)) + stT76 132 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 131
    simpa using h
  have hprev := st76_p131
  have hstep := st76_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p133 : ((2876548100903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT76 (i+1))
      = (∑ i ∈ Finset.range 132, stT76 (i+1)) + stT76 133 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 132
    simpa using h
  have hprev := st76_p132
  have hstep := st76_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p134 : ((5607199958003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT76 (i+1))
      = (∑ i ∈ Finset.range 133, stT76 (i+1)) + stT76 134 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 133
    simpa using h
  have hprev := st76_p133
  have hstep := st76_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p135 : ((5030194269543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT76 (i+1))
      = (∑ i ∈ Finset.range 134, stT76 (i+1)) + stT76 135 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 134
    simpa using h
  have hprev := st76_p134
  have hstep := st76_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p136 : ((420492499899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT76 (i+1))
      = (∑ i ∈ Finset.range 135, stT76 (i+1)) + stT76 136 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 135
    simpa using h
  have hprev := st76_p135
  have hstep := st76_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p137 : ((1692085303923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT76 (i+1))
      = (∑ i ∈ Finset.range 136, stT76 (i+1)) + stT76 137 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 136
    simpa using h
  have hprev := st76_p136
  have hstep := st76_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p138 : ((1406173615333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT76 (i+1))
      = (∑ i ∈ Finset.range 137, stT76 (i+1)) + stT76 138 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 137
    simpa using h
  have hprev := st76_p137
  have hstep := st76_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p139 : ((331749005093/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT76 (i+1))
      = (∑ i ∈ Finset.range 138, stT76 (i+1)) + stT76 139 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 138
    simpa using h
  have hprev := st76_p138
  have hstep := st76_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p140 : ((1474672736831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT76 (i+1))
      = (∑ i ∈ Finset.range 139, stT76 (i+1)) + stT76 140 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 139
    simpa using h
  have hprev := st76_p139
  have hstep := st76_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p141 : ((450990760373/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT76 (i+1))
      = (∑ i ∈ Finset.range 140, stT76 (i+1)) + stT76 141 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 140
    simpa using h
  have hprev := st76_p140
  have hstep := st76_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p142 : ((221967484691/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT76 (i+1))
      = (∑ i ∈ Finset.range 141, stT76 (i+1)) + stT76 142 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 141
    simpa using h
  have hprev := st76_p141
  have hstep := st76_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p143 : ((1302576988341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT76 (i+1))
      = (∑ i ∈ Finset.range 142, stT76 (i+1)) + stT76 143 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 142
    simpa using h
  have hprev := st76_p142
  have hstep := st76_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p144 : ((5710298586701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT76 (i+1))
      = (∑ i ∈ Finset.range 143, stT76 (i+1)) + stT76 144 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 143
    simpa using h
  have hprev := st76_p143
  have hstep := st76_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p145 : ((1161538182001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT76 (i+1))
      = (∑ i ∈ Finset.range 144, stT76 (i+1)) + stT76 145 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 144
    simpa using h
  have hprev := st76_p144
  have hstep := st76_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p146 : ((5481753183813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT76 (i+1))
      = (∑ i ∈ Finset.range 145, stT76 (i+1)) + stT76 146 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 145
    simpa using h
  have hprev := st76_p145
  have hstep := st76_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p147 : ((2411878542657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT76 (i+1))
      = (∑ i ∈ Finset.range 146, stT76 (i+1)) + stT76 147 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 146
    simpa using h
  have hprev := st76_p146
  have hstep := st76_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p148 : ((4008874808049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT76 (i+1))
      = (∑ i ∈ Finset.range 147, stT76 (i+1)) + stT76 148 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 147
    simpa using h
  have hprev := st76_p147
  have hstep := st76_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p149 : ((3247969668753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT76 (i+1))
      = (∑ i ∈ Finset.range 148, stT76 (i+1)) + stT76 149 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 148
    simpa using h
  have hprev := st76_p148
  have hstep := st76_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p150 : ((2732827014507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT76 (i+1))
      = (∑ i ∈ Finset.range 149, stT76 (i+1)) + stT76 150 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 149
    simpa using h
  have hprev := st76_p149
  have hstep := st76_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p151 : ((129447333897/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT76 (i+1))
      = (∑ i ∈ Finset.range 150, stT76 (i+1)) + stT76 151 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 150
    simpa using h
  have hprev := st76_p150
  have hstep := st76_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p152 : ((2847105002793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT76 (i+1))
      = (∑ i ∈ Finset.range 151, stT76 (i+1)) + stT76 152 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 151
    simpa using h
  have hprev := st76_p151
  have hstep := st76_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p153 : ((3439443231057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT76 (i+1))
      = (∑ i ∈ Finset.range 152, stT76 (i+1)) + stT76 153 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 152
    simpa using h
  have hprev := st76_p152
  have hstep := st76_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p154 : ((4219501490073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT76 (i+1))
      = (∑ i ∈ Finset.range 153, stT76 (i+1)) + stT76 154 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 153
    simpa using h
  have hprev := st76_p153
  have hstep := st76_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p155 : ((4999933167043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT76 (i+1))
      = (∑ i ∈ Finset.range 154, stT76 (i+1)) + stT76 155 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 154
    simpa using h
  have hprev := st76_p154
  have hstep := st76_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p156 : ((5597945594563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT76 (i+1))
      = (∑ i ∈ Finset.range 155, stT76 (i+1)) + stT76 156 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 155
    simpa using h
  have hprev := st76_p155
  have hstep := st76_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p157 : ((5877455263913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT76 (i+1))
      = (∑ i ∈ Finset.range 156, stT76 (i+1)) + stT76 157 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 156
    simpa using h
  have hprev := st76_p156
  have hstep := st76_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p158 : ((5778485462039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT76 (i+1))
      = (∑ i ∈ Finset.range 157, stT76 (i+1)) + stT76 158 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 157
    simpa using h
  have hprev := st76_p157
  have hstep := st76_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p159 : ((213117089727/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT76 (i+1))
      = (∑ i ∈ Finset.range 158, stT76 (i+1)) + stT76 159 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 158
    simpa using h
  have hprev := st76_p158
  have hstep := st76_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p160 : ((185215660831/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT76 (i+1))
      = (∑ i ∈ Finset.range 159, stT76 (i+1)) + stT76 160 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 159
    simpa using h
  have hprev := st76_p159
  have hstep := st76_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p161 : ((3842349874543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT76 (i+1))
      = (∑ i ∈ Finset.range 160, stT76 (i+1)) + stT76 161 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 160
    simpa using h
  have hprev := st76_p160
  have hstep := st76_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p162 : ((1568108698609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT76 (i+1))
      = (∑ i ∈ Finset.range 161, stT76 (i+1)) + stT76 162 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 161
    simpa using h
  have hprev := st76_p161
  have hstep := st76_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p163 : ((2662705575539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT76 (i+1))
      = (∑ i ∈ Finset.range 162, stT76 (i+1)) + stT76 163 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 162
    simpa using h
  have hprev := st76_p162
  have hstep := st76_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p164 : ((629893267177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT76 (i+1))
      = (∑ i ∈ Finset.range 163, stT76 (i+1)) + stT76 164 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 163
    simpa using h
  have hprev := st76_p163
  have hstep := st76_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p165 : ((1366483966993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT76 (i+1))
      = (∑ i ∈ Finset.range 164, stT76 (i+1)) + stT76 165 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 164
    simpa using h
  have hprev := st76_p164
  have hstep := st76_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p166 : ((1627258724743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT76 (i+1))
      = (∑ i ∈ Finset.range 165, stT76 (i+1)) + stT76 166 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 165
    simpa using h
  have hprev := st76_p165
  have hstep := st76_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p167 : ((496730398861/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT76 (i+1))
      = (∑ i ∈ Finset.range 166, stT76 (i+1)) + stT76 167 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 166
    simpa using h
  have hprev := st76_p166
  have hstep := st76_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p168 : ((296442122531/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT76 (i+1))
      = (∑ i ∈ Finset.range 167, stT76 (i+1)) + stT76 168 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 167
    simpa using h
  have hprev := st76_p167
  have hstep := st76_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p169 : ((2703877032523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT76 (i+1))
      = (∑ i ∈ Finset.range 168, stT76 (i+1)) + stT76 169 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 168
    simpa using h
  have hprev := st76_p168
  have hstep := st76_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p170 : ((2918818693523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT76 (i+1))
      = (∑ i ∈ Finset.range 169, stT76 (i+1)) + stT76 170 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 169
    simpa using h
  have hprev := st76_p169
  have hstep := st76_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p171 : ((5951348808189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT76 (i+1))
      = (∑ i ∈ Finset.range 170, stT76 (i+1)) + stT76 171 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 170
    simpa using h
  have hprev := st76_p170
  have hstep := st76_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p172 : ((1146092747201/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT76 (i+1))
      = (∑ i ∈ Finset.range 171, stT76 (i+1)) + stT76 172 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 171
    simpa using h
  have hprev := st76_p171
  have hstep := st76_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p173 : ((5220909414801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT76 (i+1))
      = (∑ i ∈ Finset.range 172, stT76 (i+1)) + stT76 173 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 172
    simpa using h
  have hprev := st76_p172
  have hstep := st76_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p174 : ((4522122564363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT76 (i+1))
      = (∑ i ∈ Finset.range 173, stT76 (i+1)) + stT76 174 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 173
    simpa using h
  have hprev := st76_p173
  have hstep := st76_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p175 : ((3766678870781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT76 (i+1))
      = (∑ i ∈ Finset.range 174, stT76 (i+1)) + stT76 175 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 174
    simpa using h
  have hprev := st76_p174
  have hstep := st76_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p176 : ((3094683384723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT76 (i+1))
      = (∑ i ∈ Finset.range 175, stT76 (i+1)) + stT76 176 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 175
    simpa using h
  have hprev := st76_p175
  have hstep := st76_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p177 : ((2627916610899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT76 (i+1))
      = (∑ i ∈ Finset.range 176, stT76 (i+1)) + stT76 177 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 176
    simpa using h
  have hprev := st76_p176
  have hstep := st76_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p178 : ((2448421685667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT76 (i+1))
      = (∑ i ∈ Finset.range 177, stT76 (i+1)) + stT76 178 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 177
    simpa using h
  have hprev := st76_p177
  have hstep := st76_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p179 : ((323141971119/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT76 (i+1))
      = (∑ i ∈ Finset.range 178, stT76 (i+1)) + stT76 179 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 178
    simpa using h
  have hprev := st76_p178
  have hstep := st76_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p180 : ((3010495705707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT76 (i+1))
      = (∑ i ∈ Finset.range 179, stT76 (i+1)) + stT76 180 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 179
    simpa using h
  have hprev := st76_p179
  have hstep := st76_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p181 : ((3647089852007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT76 (i+1))
      = (∑ i ∈ Finset.range 180, stT76 (i+1)) + stT76 181 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 180
    simpa using h
  have hprev := st76_p180
  have hstep := st76_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p182 : ((4382646059687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT76 (i+1))
      = (∑ i ∈ Finset.range 181, stT76 (i+1)) + stT76 182 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 181
    simpa using h
  have hprev := st76_p181
  have hstep := st76_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p183 : ((5090362939109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT76 (i+1))
      = (∑ i ∈ Finset.range 182, stT76 (i+1)) + stT76 183 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 182
    simpa using h
  have hprev := st76_p182
  have hstep := st76_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p184 : ((5650837876703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT76 (i+1))
      = (∑ i ∈ Finset.range 183, stT76 (i+1)) + stT76 184 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 183
    simpa using h
  have hprev := st76_p183
  have hstep := st76_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p185 : ((1194366902949/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT76 (i+1))
      = (∑ i ∈ Finset.range 184, stT76 (i+1)) + stT76 185 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 184
    simpa using h
  have hprev := st76_p184
  have hstep := st76_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p186 : ((600270884089/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT76 (i+1))
      = (∑ i ∈ Finset.range 185, stT76 (i+1)) + stT76 186 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 185
    simpa using h
  have hprev := st76_p185
  have hstep := st76_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p187 : ((1148282805779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT76 (i+1))
      = (∑ i ∈ Finset.range 186, stT76 (i+1)) + stT76 187 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 186
    simpa using h
  have hprev := st76_p186
  have hstep := st76_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p188 : ((1046663327959/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT76 (i+1))
      = (∑ i ∈ Finset.range 187, stT76 (i+1)) + stT76 188 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 187
    simpa using h
  have hprev := st76_p187
  have hstep := st76_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p189 : ((4562443530681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT76 (i+1))
      = (∑ i ∈ Finset.range 188, stT76 (i+1)) + stT76 189 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 188
    simpa using h
  have hprev := st76_p188
  have hstep := st76_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p190 : ((3836936060647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT76 (i+1))
      = (∑ i ∈ Finset.range 189, stT76 (i+1)) + stT76 190 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 189
    simpa using h
  have hprev := st76_p189
  have hstep := st76_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p191 : ((3171310735247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT76 (i+1))
      = (∑ i ∈ Finset.range 190, stT76 (i+1)) + stT76 191 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 190
    simpa using h
  have hprev := st76_p190
  have hstep := st76_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p192 : ((2668436371783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT76 (i+1))
      = (∑ i ∈ Finset.range 191, stT76 (i+1)) + stT76 192 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 191
    simpa using h
  have hprev := st76_p191
  have hstep := st76_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p193 : ((2404045075719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT76 (i+1))
      = (∑ i ∈ Finset.range 192, stT76 (i+1)) + stT76 193 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 192
    simpa using h
  have hprev := st76_p192
  have hstep := st76_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p194 : ((2416006255999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT76 (i+1))
      = (∑ i ∈ Finset.range 193, stT76 (i+1)) + stT76 194 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 193
    simpa using h
  have hprev := st76_p193
  have hstep := st76_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p195 : ((2699749241763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT76 (i+1))
      = (∑ i ∈ Finset.range 194, stT76 (i+1)) + stT76 195 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 194
    simpa using h
  have hprev := st76_p194
  have hstep := st76_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p196 : ((200638626063/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT76 (i+1))
      = (∑ i ∈ Finset.range 195, stT76 (i+1)) + stT76 196 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 195
    simpa using h
  have hprev := st76_p195
  have hstep := st76_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p197 : ((1934870404479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT76 (i+1))
      = (∑ i ∈ Finset.range 196, stT76 (i+1)) + stT76 197 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 196
    simpa using h
  have hprev := st76_p196
  have hstep := st76_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p198 : ((4580370722163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT76 (i+1))
      = (∑ i ∈ Finset.range 197, stT76 (i+1)) + stT76 198 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 197
    simpa using h
  have hprev := st76_p197
  have hstep := st76_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p199 : ((5238684404909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT76 (i+1))
      = (∑ i ∈ Finset.range 198, stT76 (i+1)) + stT76 199 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 198
    simpa using h
  have hprev := st76_p198
  have hstep := st76_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_p200 : ((5750788247759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT76 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT76 (i+1))
      = (∑ i ∈ Finset.range 199, stT76 (i+1)) + stT76 200 := by
    have h := Finset.sum_range_succ (fun i => stT76 (i+1)) 199
    simpa using h
  have hprev := st76_p199
  have hstep := st76_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st76_s200 :
    |Real.sin (((76 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-106277/500000 : ℚ) : ℝ))
      - ((689511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 380407/2000000) (δ := 487/100000000) (ψ := -106277/500000) 76 64
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 76`** (evaluated boundary). -/
theorem station_76_sign : 0 < hardyG (((76:ℕ)):ℝ) := by
  have hcore := phase_station_lower_eval 76 200 (by norm_num) (by norm_num)
    ((-106277/500000 : ℚ) : ℝ)
  have hchain := st76_p200
  have hbridge : (∑ i ∈ Finset.range 200, stT76 (i+1))
      = ∑ i ∈ Finset.range 200,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((76:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-106277/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_200
  have hsh := rpow_half_shifts (N := 200) (by norm_num)
  -- boundary lower bound via the two certificates
  have hcosb := abs_le.mp st76_c200
  have hsinb := abs_le.mp st76_s200
  have hbdy_lo : ((-74626373601879/577625000000000 : ℚ) : ℝ)
      ≤ ((200:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos ((((76:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((-106277/500000 : ℚ) : ℝ))) / 2
          - (((76:ℕ)):ℝ)
            * Real.sin ((((76:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((-106277/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + (((76:ℕ)):ℝ) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((76:ℝ) * Real.log (200:ℝ) - ((-106277/500000 : ℚ) : ℝ))) / 2
        - (76:ℝ) * Real.sin ((76:ℝ) * Real.log (200:ℝ) - ((-106277/500000 : ℚ) : ℝ))
        ≥ ((-105537597/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hEneg : -(Real.cos ((76:ℝ) * Real.log (200:ℝ) - ((-106277/500000 : ℚ) : ℝ))) / 2
        - (76:ℝ) * Real.sin ((76:ℝ) * Real.log (200:ℝ) - ((-106277/500000 : ℚ) : ℝ))
        ≤ 0 := by
      nlinarith [hcosb.1, hsinb.1, Real.neg_one_le_cos ((76:ℝ) * Real.log (200:ℝ) - ((-106277/500000 : ℚ) : ℝ)), Real.neg_one_le_sin ((76:ℝ) * Real.log (200:ℝ) - ((-106277/500000 : ℚ) : ℝ))]
    have hsqpos : (0:ℝ) ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (200:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + (76:ℝ) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-105537597/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (200:ℝ) * (707107/10000000)
          * ((-105537597/2000000 : ℚ) : ℝ)
        ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ)))
          * ((-105537597/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((200:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((76:ℕ)):ℝ)+1) * ((((76:ℕ)):ℝ)+2) / 8
        * (((200:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((200:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((341817645121/1600000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((5750788247759/10000000000000 : ℚ) : ℝ) + ((-74626373601879/577625000000000 : ℚ) : ℝ)
      - ((341817645121/1600000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-106277/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((76:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-106277/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((76:ℕ)):ℝ))).re
      - Real.sin ((-106277/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((76:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((76:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((76:ℕ)):ℝ)
      = ((((76:ℕ)):ℝ) * (Real.log (((76:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((76:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_76
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
  have hθwin : |(((-106277/500000 : ℚ) : ℝ) + ((9:ℤ)) * (2*Real.pi))
      - theta (((76:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((76:ℕ)):ℝ))
    (φ := ((-106277/500000 : ℚ) : ℝ) + ((9:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-106277/500000 : ℚ)) : ℝ) 9).1,
    (cos_sin_shift (((-106277/500000 : ℚ)) : ℝ) 9).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_76_sign
end AxiomAudit
