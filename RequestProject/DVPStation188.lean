import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 188` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT188 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((188 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-55451/50000 : ℚ) : ℝ))

theorem st188_c1 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((445539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55451/200000) (δ := 1/1000000000) (ψ := -55451/50000) 188 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t1 : ((445489/1000000 : ℚ) : ℝ) ≤ stT188 1 := by
  have hc : ((445489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((445489/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((445489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c2 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((432359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -657759/5000000) (δ := 2363/250000000) (ψ := -55451/50000) 188 21
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t2 : ((1528531340189/2500000000000 : ℚ) : ℝ) ≤ stT188 2 := by
  have hc : ((216167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1528531340189/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((216167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c3 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((954443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9469/125000) (δ := 4769/500000000) (ψ := -55451/50000) 188 33
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t3 : ((2755094947143/5000000000000 : ℚ) : ℝ) ≤ stT188 3 := by
  have hc : ((954393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2755094947143/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((954393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c4 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-556883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5403563/10000000) (δ := 19/2000000) (ψ := -55451/50000) 188 42
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t4 : ((-2784665556933/10000000000000 : ℚ) : ℝ) ≤ stT188 4 := by
  have hc : ((-556933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2784665556933/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-556933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c5 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-124147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104523/200000) (δ := 4773/500000000) (ψ := -55451/50000) 188 48
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t5 : ((-138814542423/625000000000 : ℚ) : ℝ) ≤ stT188 5 := by
  have hc : ((-248319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138814542423/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-248319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c6 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((236329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133221/400000) (δ := 4707/500000000) (ψ := -55451/50000) 188 54
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t6 : ((482302382239/5000000000000 : ℚ) : ℝ) ≤ stT188 6 := by
  have hc : ((236279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482302382239/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((236279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c7 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-810253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6288451/10000000) (δ := 4709/500000000) (ψ := -55451/50000) 188 58
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t7 : ((-612531536487/2000000000000 : ℚ) : ℝ) ≤ stT188 7 := by
  have hc : ((-810303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-612531536487/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-810303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c8 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-793017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1554089/2500000) (δ := 9447/1000000000) (ψ := -55451/50000) 188 62
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t8 : ((-1401957671389/5000000000000 : ℚ) : ℝ) ≤ stT188 8 := by
  have hc : ((-793067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1401957671389/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-793067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c9 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((876143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257487/10000000) (δ := 379/40000000) (ψ := -55451/50000) 188 66
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t9 : ((2920309707969/10000000000000 : ℚ) : ℝ) ≤ stT188 9 := by
  have hc : ((876093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2920309707969/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((876093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c10 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((898163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 569029/5000000) (δ := 4703/500000000) (ψ := -55451/50000) 188 69
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t10 : ((2840082083301/10000000000000 : ℚ) : ℝ) ≤ stT188 10 := by
  have hc : ((898113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2840082083301/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((898113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c11 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((222207/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -595019/5000000) (δ := 1897/200000000) (ψ := -55451/50000) 188 72
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t11 : ((1339883050957/5000000000000 : ℚ) : ℝ) ≤ stT188 11 := by
  have hc : ((444389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1339883050957/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((444389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c12 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-123109/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -741857/1000000) (δ := 9563/1000000000) (ψ := -55451/50000) 188 75
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t12 : ((-44425399271/156250000000 : ℚ) : ℝ) ≤ stT188 12 := by
  have hc : ((-492461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44425399271/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-492461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c13 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((176863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1214427/10000000) (δ := 4727/500000000) (ψ := -55451/50000) 188 77
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t13 : ((981003591/4000000000 : ℚ) : ℝ) ≤ stT188 13 := by
  have hc : ((176853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((981003591/4000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((176853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c14 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((318513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1100203/5000000) (δ := 4767/500000000) (ψ := -55451/50000) 188 79
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t14 : ((26599839083/156250000000 : ℚ) : ℝ) ≤ stT188 14 := by
  have hc : ((39811/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26599839083/156250000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((39811/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c15 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((141221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3211143/10000000) (δ := 9483/1000000000) (ψ := -55451/50000) 188 81
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t15 : ((22785398603/312500000000 : ℚ) : ℝ) ≤ stT188 15 := by
  have hc : ((35299/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22785398603/312500000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((35299/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c16 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((164747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2128311/10000000) (δ := 4753/500000000) (ψ := -55451/50000) 188 83
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t16 : ((329469/2000000 : ℚ) : ℝ) ≤ stT188 16 := by
  have hc : ((329469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329469/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((329469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c17 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((949981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794053/10000000) (δ := 1189/125000000) (ψ := -55451/50000) 188 85
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t17 : ((575980212609/2500000000000 : ℚ) : ℝ) ≤ stT188 17 := by
  have hc : ((949931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((575980212609/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((949931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c18 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-107491/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1336383/2500000) (δ := 9477/1000000000) (ψ := -55451/50000) 188 87
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t18 : ((-253382329523/2000000000000 : ℚ) : ℝ) ≤ stT188 18 := by
  have hc : ((-107501/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253382329523/2000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-107501/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c19 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-85793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4358089/10000000) (δ := 9433/1000000000) (ψ := -55451/50000) 188 88
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t19 : ((-49220012811/1250000000000 : ℚ) : ℝ) ≤ stT188 19 := by
  have hc : ((-42909/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49220012811/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-42909/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c20 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((38093/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2949987/10000000) (δ := 1911/200000000) (ψ := -55451/50000) 188 90
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t20 : ((10645914987/125000000000 : ℚ) : ℝ) ≤ stT188 20 := by
  have hc : ((4761/12500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10645914987/125000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((4761/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c21 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-69069/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1068361/2500000) (δ := 1181/125000000) (ψ := -55451/50000) 188 91
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t21 : ((-75387737913/2500000000000 : ℚ) : ℝ) ≤ stT188 21 := by
  have hc : ((-34547/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75387737913/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-34547/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c22 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-51451/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2639041/5000000) (δ := 9569/1000000000) (ψ := -55451/50000) 188 93
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t22 : ((-53566701/488281250 : ℚ) : ℝ) ≤ stT188 22 := by
  have hc : ((-1608/3125 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53566701/488281250 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-1608/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c23 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((499649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -937/100000) (δ := 9527/1000000000) (ψ := -55451/50000) 188 94
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t23 : ((16277937279/78125000000 : ℚ) : ℝ) ≤ stT188 23 := by
  have hc : ((62453/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16277937279/78125000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((62453/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c24 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-109523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4201349/10000000) (δ := 9419/1000000000) (ψ := -55451/50000) 188 95
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t24 : ((-111832504833/5000000000000 : ℚ) : ℝ) ≤ stT188 24 := by
  have hc : ((-109573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111832504833/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-109573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c25 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-249393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3839863/5000000) (δ := 9491/1000000000) (ψ := -55451/50000) 188 96
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t25 : ((-997622498811/5000000000000 : ℚ) : ℝ) ≤ stT188 25 := by
  have hc : ((-498811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-997622498811/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-498811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c26 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-522851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -662809/1250000) (δ := 4749/500000000) (ψ := -55451/50000) 188 98
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t26 : ((-512746785481/5000000000000 : ℚ) : ℝ) ≤ stT188 26 := by
  have hc : ((-522901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512746785481/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-522901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c27 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((129409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1636247/5000000) (δ := 2353/250000000) (ψ := -55451/50000) 188 99
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t27 : ((62249877/1250000000 : ℚ) : ℝ) ≤ stT188 27 := by
  have hc : ((16173/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62249877/1250000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((16173/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c28 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((364117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -943819/5000000) (δ := 9519/1000000000) (ψ := -55451/50000) 188 100
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t28 : ((86008633953/625000000000 : ℚ) : ℝ) ≤ stT188 28 := by
  have hc : ((91023/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86008633953/625000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((91023/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c29 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((904293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102691/10000000) (δ := 1197/125000000) (ψ := -55451/50000) 188 101
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t29 : ((1679136751579/10000000000000 : ℚ) : ℝ) ≤ stT188 29 := by
  have hc : ((904243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1679136751579/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((904243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c30 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((187821/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -876949/10000000) (δ := 9469/1000000000) (ψ := -55451/50000) 188 102
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t30 : ((342894242951/2000000000000 : ℚ) : ℝ) ≤ stT188 30 := by
  have hc : ((187811/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342894242951/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((187811/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c31 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((891811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173659/10000000) (δ := 9441/1000000000) (ψ := -55451/50000) 188 103
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t31 : ((1601650019333/10000000000000 : ℚ) : ℝ) ≤ stT188 31 := by
  have hc : ((891761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1601650019333/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((891761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c32 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((70817/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1959733/10000000) (δ := 2387/250000000) (ψ := -55451/50000) 188 104
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t32 : ((15647380749/125000000000 : ℚ) : ℝ) ≤ stT188 32 := by
  have hc : ((17703/25000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15647380749/125000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((17703/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c33 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((284781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641009/2000000) (δ := 2387/250000000) (ψ := -55451/50000) 188 105
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t33 : ((61956611407/1250000000000 : ℚ) : ℝ) ≤ stT188 33 := by
  have hc : ((284731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61956611407/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((284731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c34 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-372817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2441049/5000000) (δ := 59/6250000) (ψ := -55451/50000) 188 106
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t34 : ((-319730842431/5000000000000 : ℚ) : ℝ) ≤ stT188 34 := by
  have hc : ((-372867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319730842431/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-372867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c35 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-937571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435371/625000) (δ := 947/100000000) (ψ := -55451/50000) 188 107
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t35 : ((-1584869214889/10000000000000 : ℚ) : ℝ) ≤ stT188 35 := by
  have hc : ((-937621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1584869214889/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-937621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c36 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-806943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6274387/10000000) (δ := 947/100000000) (ψ := -55451/50000) 188 107
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t36 : ((-1344988602331/10000000000000 : ℚ) : ℝ) ≤ stT188 36 := by
  have hc : ((-806993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1344988602331/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-806993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c37 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((38403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1721977/5000000) (δ := 9577/1000000000) (ψ := -55451/50000) 188 108
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t37 : ((63117669677/2000000000000 : ℚ) : ℝ) ≤ stT188 37 := by
  have hc : ((38393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63117669677/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((38393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c38 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((248543/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67511/2500000) (δ := 9519/1000000000) (ψ := -55451/50000) 188 109
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t38 : ((403169656527/2500000000000 : ℚ) : ℝ) ≤ stT188 38 := by
  have hc : ((497061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((403169656527/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((497061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c39 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((34427/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1614717/5000000) (δ := 2353/250000000) (ψ := -55451/50000) 188 110
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t39 : ((220469171923/5000000000000 : ℚ) : ℝ) ≤ stT188 39 := by
  have hc : ((137683/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220469171923/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((137683/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c40 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-947209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7038031/10000000) (δ := 4749/500000000) (ψ := -55451/50000) 188 111
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t40 : ((-1497748148001/10000000000000 : ℚ) : ℝ) ≤ stT188 40 := by
  have hc : ((-947259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1497748148001/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-947259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c41 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-126703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4567491/10000000) (δ := 4749/500000000) (ψ := -55451/50000) 188 111
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t41 : ((-12369745829/312500000000 : ℚ) : ℝ) ≤ stT188 41 := by
  have hc : ((-15841/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12369745829/312500000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-15841/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c42 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((997251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 185399/10000000) (δ := 9597/1000000000) (ψ := -55451/50000) 188 112
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t42 : ((1538714050633/10000000000000 : ℚ) : ℝ) ≤ stT188 42 := by
  have hc : ((997201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1538714050633/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((997201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c43 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-106427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4463229/10000000) (δ := 949/100000000) (ψ := -55451/50000) 188 113
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t43 : ((-20292226209/625000000000 : ℚ) : ℝ) ≤ stT188 43 := by
  have hc : ((-26613/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20292226209/625000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-26613/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c44 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-822583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1585459/2500000) (δ := 949/100000000) (ψ := -55451/50000) 188 113
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t44 : ((-1240166137581/10000000000000 : ℚ) : ℝ) ≤ stT188 44 := by
  have hc : ((-822633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1240166137581/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-822633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c45 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((221929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1196089/10000000) (δ := 471/50000000) (ψ := -55451/50000) 188 114
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t45 : ((661626735263/5000000000000 : ℚ) : ℝ) ≤ stT188 45 := by
  have hc : ((443833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661626735263/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((443833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c46 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-6359/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4181791/10000000) (δ := 9527/1000000000) (ψ := -55451/50000) 188 115
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t46 : ((-3752177737/250000000000 : ℚ) : ℝ) ≤ stT188 46 := by
  have hc : ((-50897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3752177737/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-50897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c47 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-717127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 592617/1000000) (δ := 9527/1000000000) (ψ := -55451/50000) 188 115
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t47 : ((-20922204621/200000000000 : ℚ) : ℝ) ≤ stT188 47 := by
  have hc : ((-717177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20922204621/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-717177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c48 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((998973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14163/1250000) (δ := 9569/1000000000) (ψ := -55451/50000) 188 116
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t48 : ((11534563881/80000000000 : ℚ) : ℝ) ≤ stT188 48 := by
  have hc : ((998923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11534563881/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((998923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c49 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-22213/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1180727/2000000) (δ := 9461/1000000000) (ψ := -55451/50000) 188 117
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t49 : ((-126940407919/1250000000000 : ℚ) : ℝ) ≤ stT188 49 := by
  have hc : ((-355433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126940407919/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-355433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c50 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((66861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3591681/10000000) (δ := 9461/1000000000) (ψ := -55451/50000) 188 117
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t50 : ((23630085017/1250000000000 : ℚ) : ℝ) ≤ stT188 50 := by
  have hc : ((16709/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23630085017/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((16709/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c51 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((216209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140453/500000) (δ := 9449/1000000000) (ψ := -55451/50000) 188 118
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t51 : ((945994161/15625000000 : ℚ) : ℝ) ≤ stT188 51 := by
  have hc : ((27023/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((945994161/15625000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((27023/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c52 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-204249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6317447/10000000) (δ := 9449/1000000000) (ψ := -55451/50000) 188 118
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t52 : ((-566519678773/5000000000000 : ℚ) : ℝ) ≤ stT188 52 := by
  have hc : ((-408523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-566519678773/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-408523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c53 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((984701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218931/5000000) (δ := 2389/250000000) (ψ := -55451/50000) 188 119
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t53 : ((270504307371/2000000000000 : ℚ) : ℝ) ≤ stT188 53 := by
  have hc : ((984651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270504307371/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((984651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c54 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-122573/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7360539/10000000) (δ := 477/50000000) (ψ := -55451/50000) 188 120
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t54 : ((-166809275619/1250000000000 : ℚ) : ℝ) ≤ stT188 54 := by
  have hc : ((-490317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166809275619/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-490317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c55 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((437487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 631769/5000000) (δ := 477/50000000) (ψ := -55451/50000) 188 120
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t55 : ((294936661669/2500000000000 : ℚ) : ℝ) ≤ stT188 55 := by
  have hc : ((218731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294936661669/2500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((218731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c56 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-365401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -597573/1000000) (δ := 9433/1000000000) (ψ := -55451/50000) 188 121
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t56 : ((-244160660891/2500000000000 : ℚ) : ℝ) ≤ stT188 56 := by
  have hc : ((-182713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244160660891/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-182713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c57 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((29601/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1171541/5000000) (δ := 9433/1000000000) (ψ := -55451/50000) 188 121
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t57 : ((19602080201/250000000000 : ℚ) : ℝ) ≤ stT188 57 := by
  have hc : ((59197/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19602080201/250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((59197/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c58 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-484243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1038147/2000000) (δ := 9477/1000000000) (ψ := -55451/50000) 188 122
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t58 : ((-127181637609/2000000000000 : ℚ) : ℝ) ≤ stT188 58 := by
  have hc : ((-484293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127181637609/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-484293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c59 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((419907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2843633/10000000) (δ := 9477/1000000000) (ψ := -55451/50000) 188 122
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t59 : ((546607209873/10000000000000 : ℚ) : ℝ) ≤ stT188 59 := by
  have hc : ((419857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((546607209873/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((419857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c60 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-201687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4964993/10000000) (δ := 1917/200000000) (ψ := -55451/50000) 188 123
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t60 : ((-3255114793/62500000000 : ℚ) : ℝ) ≤ stT188 60 := by
  have hc : ((-12607/31250 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3255114793/62500000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-12607/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c61 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((217161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1401889/5000000) (δ := 1917/200000000) (ψ := -55451/50000) 188 123
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t61 : ((1085992133/19531250000 : ℚ) : ℝ) ≤ stT188 61 := by
  have hc : ((13571/31250 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1085992133/19531250000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((13571/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c62 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-254449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5261751/10000000) (δ := 9511/1000000000) (ψ := -55451/50000) 188 124
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t62 : ((-80795622237/1250000000000 : ℚ) : ℝ) ≤ stT188 62 := by
  have hc : ((-127237/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80795622237/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-127237/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c63 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((618963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2258437/10000000) (δ := 9511/1000000000) (ψ := -55451/50000) 188 124
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t63 : ((779756729353/10000000000000 : ℚ) : ℝ) ≤ stT188 63 := by
  have hc : ((618913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((779756729353/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((618913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c64 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-37509/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241913/400000) (δ := 2351/250000000) (ψ := -55451/50000) 188 125
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t64 : ((-93778825023/1000000000000 : ℚ) : ℝ) ≤ stT188 64 := by
  have hc : ((-75023/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93778825023/1000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-75023/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c65 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((175931/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239149/10000000) (δ := 2351/250000000) (ψ := -55451/50000) 188 125
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t65 : ((218203084587/2000000000000 : ℚ) : ℝ) ≤ stT188 65 := by
  have hc : ((175921/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218203084587/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((175921/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c66 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-974937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7293089/10000000) (δ := 4753/500000000) (ψ := -55451/50000) 188 126
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t66 : ((-240025224621/2000000000000 : ℚ) : ℝ) ≤ stT188 66 := by
  have hc : ((-974987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240025224621/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-974987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c67 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((995943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56319/2500000) (δ := 4753/500000000) (ψ := -55451/50000) 188 126
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t67 : ((608338251371/5000000000000 : ℚ) : ℝ) ≤ stT188 67 := by
  have hc : ((995893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((608338251371/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((995893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c68 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-901979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6737821/10000000) (δ := 4753/500000000) (ψ := -55451/50000) 188 126
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t68 : ((-1093871625691/10000000000000 : ℚ) : ℝ) ≤ stT188 68 := by
  have hc : ((-902029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1093871625691/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-902029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c69 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((132973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2108707/10000000) (δ := 959/100000000) (ψ := -55451/50000) 188 127
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t69 : ((80034285627/1000000000000 : ℚ) : ℝ) ≤ stT188 69 := by
  have hc : ((132963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80034285627/1000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((132963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c70 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-57343/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2326991/5000000) (δ := 959/100000000) (ψ := -55451/50000) 188 127
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t70 : ((-68549968837/2000000000000 : ℚ) : ℝ) ≤ stT188 70 := by
  have hc : ((-57353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68549968837/2000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-57353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c71 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-183053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4387219/10000000) (δ := 9483/1000000000) (ψ := -55451/50000) 188 128
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t71 : ((-108651672273/5000000000000 : ℚ) : ℝ) ≤ stT188 71 := by
  have hc : ((-183103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108651672273/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-183103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c72 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((80169/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1093171/5000000) (δ := 9483/1000000000) (ψ := -55451/50000) 188 128
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t72 : ((377890730661/5000000000000 : ℚ) : ℝ) ≤ stT188 72 := by
  have hc : ((320651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377890730661/5000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((320651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c73 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-118413/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703877/1000000) (δ := 2357/250000000) (ψ := -55451/50000) 188 129
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t73 : ((-138599311231/1250000000000 : ℚ) : ℝ) ≤ stT188 73 := by
  have hc : ((-473677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138599311231/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-473677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c74 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((96699/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -322069/5000000) (δ := 2357/250000000) (ψ := -55451/50000) 188 129
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t74 : ((14050556793/125000000000 : ℚ) : ℝ) ≤ stT188 74 := by
  have hc : ((48347/50000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14050556793/125000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((48347/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c75 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-80057/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5664719/10000000) (δ := 2357/250000000) (ψ := -55451/50000) 188 129
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t75 : ((-369796459353/5000000000000 : ℚ) : ℝ) ≤ stT188 75 := by
  have hc : ((-320253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369796459353/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-320253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c76 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((43583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1909/5000) (δ := 1907/200000000) (ψ := -55451/50000) 188 130
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t76 : ((24967873287/5000000000000 : ℚ) : ℝ) ≤ stT188 76 := by
  have hc : ((43533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24967873287/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((43533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c77 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((11951/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2325887/10000000) (δ := 1907/200000000) (ψ := -55451/50000) 188 130
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t77 : ((54473119/800000000 : ℚ) : ℝ) ≤ stT188 77 := by
  have hc : ((239/400 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54473119/800000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((239/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c78 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-977061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7317479/10000000) (δ := 9561/1000000000) (ψ := -55451/50000) 188 131
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t78 : ((-553180644429/5000000000000 : ℚ) : ℝ) ≤ stT188 78 := by
  have hc : ((-977111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553180644429/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-977111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c79 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((215441/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1330149/10000000) (δ := 9561/1000000000) (ψ := -55451/50000) 188 131
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t79 : ((484751609559/5000000000000 : ℚ) : ℝ) ≤ stT188 79 := by
  have hc : ((430857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484751609559/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((430857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c80 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-258973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4581887/10000000) (δ := 9561/1000000000) (ψ := -55451/50000) 188 131
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t80 : ((-144798260391/5000000000000 : ℚ) : ℝ) ≤ stT188 80 := by
  have hc : ((-259023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144798260391/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-259023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c81 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-517737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5287501/10000000) (δ := 4727/500000000) (ψ := -55451/50000) 188 132
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t81 : ((-71914918643/1250000000000 : ℚ) : ℝ) ≤ stT188 81 := by
  have hc : ((-517787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71914918643/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-517787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c82 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((981667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239723/5000000) (δ := 4727/500000000) (ψ := -55451/50000) 188 132
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t82 : ((216802875471/2000000000000 : ℚ) : ℝ) ≤ stT188 82 := by
  have hc : ((981617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216802875471/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((981617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c83 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-391603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 772063/1250000) (δ := 4727/500000000) (ψ := -55451/50000) 188 132
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t83 : ((-107466933201/1250000000000 : ℚ) : ℝ) ≤ stT188 83 := by
  have hc : ((-97907/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107466933201/1250000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-97907/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c84 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((9729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3902669/10000000) (δ := 18947/1000000000) (ψ := -55451/50000) 188 133
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t84 : ((10560650431/10000000000000 : ℚ) : ℝ) ≤ stT188 84 := by
  have hc : ((9679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10560650431/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((9679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c85 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((787651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1659523/10000000) (δ := 591/62500000) (ψ := -55451/50000) 188 133
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t85 : ((213568249963/2500000000000 : ℚ) : ℝ) ≤ stT188 85 := by
  have hc : ((787601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213568249963/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((787601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c86 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-961349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7156643/10000000) (δ := 591/62500000) (ψ := -55451/50000) 188 133
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t86 : ((-129587932609/1250000000000 : ℚ) : ℝ) ≤ stT188 86 := by
  have hc : ((-961399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129587932609/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-961399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c87 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((318093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3117697/10000000) (δ := 2391/250000000) (ψ := -55451/50000) 188 134
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t87 : ((21311107301/625000000000 : ℚ) : ℝ) ≤ stT188 87 := by
  have hc : ((318043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21311107301/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((318043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c88 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((620421/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70431/312500) (δ := 2391/250000000) (ψ := -55451/50000) 188 134
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t88 : ((661317347113/10000000000000 : ℚ) : ℝ) ≤ stT188 88 := by
  have hc : ((620371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661317347113/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((620371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c89 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-496653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7564557/10000000) (δ := 2391/250000000) (ψ := -55451/50000) 188 134
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t89 : ((-131619421661/1250000000000 : ℚ) : ℝ) ≤ stT188 89 := by
  have hc : ((-248339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131619421661/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-248339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c90 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((402287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -722989/2500000) (δ := 2383/250000000) (ψ := -55451/50000) 188 135
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t90 : ((105998700951/2500000000000 : ℚ) : ℝ) ≤ stT188 90 := by
  have hc : ((402237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105998700951/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((402237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c91 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((605351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150737/5000000) (δ := 18871/1000000000) (ψ := -55451/50000) 188 135
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t91 : ((158631838371/2500000000000 : ℚ) : ℝ) ≤ stT188 91 := by
  have hc : ((605301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158631838371/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((605301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c92 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-986197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7438127/10000000) (δ := 2383/250000000) (ψ := -55451/50000) 188 135
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t92 : ((-1028234493531/10000000000000 : ℚ) : ℝ) ≤ stT188 92 := by
  have hc : ((-986247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1028234493531/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-986247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c93 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((145519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3188713/10000000) (δ := 377/40000000) (ψ := -55451/50000) 188 136
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t93 : ((75435074397/2500000000000 : ℚ) : ℝ) ≤ stT188 93 := by
  have hc : ((72747/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75435074397/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((72747/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c94 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((185419/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 919039/5000000) (δ := 377/40000000) (ψ := -55451/50000) 188 136
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t94 : ((382464315273/5000000000000 : ℚ) : ℝ) ≤ stT188 94 := by
  have hc : ((370813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((382464315273/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((370813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c95 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-457169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1362333/2000000) (δ := 377/40000000) (ψ := -55451/50000) 188 136
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t95 : ((-234535721463/2500000000000 : ℚ) : ℝ) ≤ stT188 95 := by
  have hc : ((-228597/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234535721463/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-228597/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c96 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-19117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3974787/10000000) (δ := 1897/200000000) (ψ := -55451/50000) 188 137
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t96 : ((-19562242707/10000000000000 : ℚ) : ℝ) ≤ stT188 96 := by
  have hc : ((-19167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19562242707/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-19167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c97 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((936497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 895729/10000000) (δ := 1897/200000000) (ψ := -55451/50000) 188 137
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t97 : ((475408857831/5000000000000 : ℚ) : ℝ) ≤ stT188 97 := by
  have hc : ((936447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((475408857831/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((936447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c98 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-656159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1429071/2500000) (δ := 1897/200000000) (ψ := -55451/50000) 188 137
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t98 : ((-662871489977/10000000000000 : ℚ) : ℝ) ≤ stT188 98 := by
  have hc : ((-656209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-662871489977/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-656209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c99 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-494469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5220051/10000000) (δ := 1199/125000000) (ψ := -55451/50000) 188 138
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t99 : ((-248505193361/5000000000000 : ℚ) : ℝ) ≤ stT188 99 := by
  have hc : ((-494519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248505193361/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-494519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c100 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((980351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49641/1000000) (δ := 1199/125000000) (ψ := -55451/50000) 188 138
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t100 : ((980300019699/10000000000000 : ℚ) : ℝ) ≤ stT188 100 := by
  have hc : ((980301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((980300019699/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((980301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c101 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-50571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2090139/5000000) (δ := 1199/125000000) (ψ := -55451/50000) 188 138
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t101 : ((-6293117831/625000000000 : ℚ) : ℝ) ≤ stT188 101 := by
  have hc : ((-12649/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6293117831/625000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-12649/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c102 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-927641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1379421/2000000) (δ := 297/31250000) (ψ := -55451/50000) 188 139
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t102 : ((-229637847067/2500000000000 : ℚ) : ℝ) ≤ stT188 102 := by
  have hc : ((-927691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229637847067/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-927691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c103 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((301039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1155869/5000000) (δ := 297/31250000) (ψ := -55451/50000) 188 139
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t103 : ((148298911803/2500000000000 : ℚ) : ℝ) ≤ stT188 103 := by
  have hc : ((150507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148298911803/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((150507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c104 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((628057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445871/2000000) (δ := 297/31250000) (ψ := -55451/50000) 188 139
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t104 : ((30790555203/500000000000 : ℚ) : ℝ) ≤ stT188 104 := by
  have hc : ((628007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30790555203/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((628007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c105 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-450053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 336351/500000) (δ := 297/31250000) (ψ := -55451/50000) 188 139
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t105 : ((-219615785139/2500000000000 : ℚ) : ℝ) ≤ stT188 105 := by
  have hc : ((-225039/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219615785139/2500000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-225039/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c106 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-2373/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2262977/5000000) (δ := 9407/1000000000) (ψ := -55451/50000) 188 140
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t106 : ((-2305347321/100000000000 : ℚ) : ℝ) ≤ stT188 106 := by
  have hc : ((-4747/20000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2305347321/100000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-4747/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c107 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((998983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28187/2500000) (δ := 9407/1000000000) (ψ := -55451/50000) 188 140
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t107 : ((60356530793/625000000000 : ℚ) : ℝ) ≤ stT188 107 := by
  have hc : ((998933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60356530793/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((998933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c108 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-33141/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212969/500000) (δ := 9407/1000000000) (ψ := -55451/50000) 188 140
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t108 : ((-63803977057/5000000000000 : ℚ) : ℝ) ≤ stT188 108 := by
  have hc : ((-66307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63803977057/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-66307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c109 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-956837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7116781/10000000) (δ := 4757/500000000) (ψ := -55451/50000) 188 141
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t109 : ((-916532204549/10000000000000 : ℚ) : ℝ) ≤ stT188 109 := by
  have hc : ((-956887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-916532204549/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-956887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c110 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((426839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1412253/5000000) (δ := 4757/500000000) (ψ := -55451/50000) 188 141
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t110 : ((203463546759/5000000000000 : ℚ) : ℝ) ≤ stT188 110 := by
  have hc : ((426789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203463546759/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((426789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c111 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((105131/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1428947/10000000) (δ := 4757/500000000) (ψ := -55451/50000) 188 141
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t111 : ((399119569343/5000000000000 : ℚ) : ℝ) ≤ stT188 111 := by
  have hc : ((420499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399119569343/5000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((420499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c112 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-634127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5644189/10000000) (δ := 4757/500000000) (ψ := -55451/50000) 188 141
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t112 : ((-37452591089/625000000000 : ℚ) : ℝ) ≤ stT188 112 := by
  have hc : ((-634177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37452591089/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-634177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c113 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-705821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1177189/2000000) (δ := 4791/500000000) (ψ := -55451/50000) 188 142
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t113 : ((-664027672991/10000000000000 : ℚ) : ℝ) ≤ stT188 113 := by
  have hc : ((-705871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-664027672991/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-705871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c114 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((766139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1744963/10000000) (δ := 4791/500000000) (ψ := -55451/50000) 188 142
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t114 : ((143501493213/2000000000000 : ℚ) : ℝ) ≤ stT188 114 := by
  have hc : ((766089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143501493213/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((766089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c115 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((586593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589969/2500000) (δ := 4791/500000000) (ψ := -55451/50000) 188 142
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t115 : ((68369211709/1250000000000 : ℚ) : ℝ) ≤ stT188 115 := by
  have hc : ((586543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68369211709/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((586543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c116 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-420967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 401821/625000) (δ := 4791/500000000) (ψ := -55451/50000) 188 142
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t116 : ((-3053760853/39062500000 : ℚ) : ℝ) ≤ stT188 116 := by
  have hc : ((-13156/15625 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3053760853/39062500000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-13156/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c117 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-20117/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5244441/10000000) (δ := 379/40000000) (ψ := -55451/50000) 188 143
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t117 : ((-18600035619/400000000000 : ℚ) : ℝ) ≤ stT188 117 := by
  have hc : ((-20119/40000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18600035619/400000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-20119/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c118 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((219663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -311103/2500000) (δ := 379/40000000) (ψ := -55451/50000) 188 143
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t118 : ((202204539387/2500000000000 : ℚ) : ℝ) ≤ stT188 118 := by
  have hc : ((439301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202204539387/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((439301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c119 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((463611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 85057/312500) (δ := 379/40000000) (ψ := -55451/50000) 188 143
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t119 : ((212472720789/5000000000000 : ℚ) : ℝ) ≤ stT188 119 := by
  have hc : ((463561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212472720789/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((463561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c120 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-887169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266197/400000) (δ := 379/40000000) (ψ := -55451/50000) 188 143
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t120 : ((-809916495749/10000000000000 : ℚ) : ℝ) ≤ stT188 120 := by
  have hc : ((-887219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-809916495749/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-887219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c121 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-235421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2576301/5000000) (δ := 1887/200000000) (ψ := -55451/50000) 188 144
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t121 : ((-107020919793/2500000000000 : ℚ) : ℝ) ≤ stT188 121 := by
  have hc : ((-117723/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107020919793/2500000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-117723/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c122 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((870929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1284267/10000000) (δ := 1887/200000000) (ψ := -55451/50000) 188 144
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t122 : ((788456398803/10000000000000 : ℚ) : ℝ) ≤ stT188 122 := by
  have hc : ((870879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((788456398803/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((870879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c123 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((522519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 638121/2500000) (δ := 1887/200000000) (ψ := -55451/50000) 188 144
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t123 : ((471094100761/10000000000000 : ℚ) : ℝ) ≤ stT188 123 := by
  have hc : ((522469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471094100761/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((522469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c124 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-20657/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794771/1250000) (δ := 1887/200000000) (ψ := -55451/50000) 188 144
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t124 : ((-74206665091/1000000000000 : ℚ) : ℝ) ≤ stT188 124 := by
  have hc : ((-82633/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74206665091/1000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-82633/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c125 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-30619/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5574661/10000000) (δ := 9543/1000000000) (ψ := -55451/50000) 188 145
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t125 : ((-13694363501/250000000000 : ℚ) : ℝ) ≤ stT188 125 := by
  have hc : ((-61243/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13694363501/250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-61243/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c126 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((92993/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1829607/10000000) (δ := 9543/1000000000) (ψ := -55451/50000) 188 145
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t126 : ((33135642389/500000000000 : ℚ) : ℝ) ≤ stT188 126 := by
  have hc : ((371947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33135642389/500000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((371947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c127 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((36437/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188579/1000000) (δ := 9543/1000000000) (ψ := -55451/50000) 188 145
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t127 : ((16165186091/250000000000 : ℚ) : ℝ) ≤ stT188 127 := by
  have hc : ((72869/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16165186091/250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((72869/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c128 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-38223/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2786047/5000000) (δ := 9543/1000000000) (ψ := -55451/50000) 188 145
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t128 : ((-67574920539/1250000000000 : ℚ) : ℝ) ≤ stT188 128 := by
  have hc : ((-305809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67574920539/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-305809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c129 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-852369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1619559/2500000) (δ := 9553/1000000000) (ψ := -55451/50000) 188 146
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t129 : ((-750513160969/10000000000000 : ℚ) : ℝ) ≤ stT188 129 := by
  have hc : ((-852419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750513160969/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-852419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c130 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((104499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22257/78125) (δ := 9553/1000000000) (ψ := -55451/50000) 188 146
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t130 : ((91640720717/2500000000000 : ℚ) : ℝ) ≤ stT188 130 := by
  have hc : ((208973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91640720717/2500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((208973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c131 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((955021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 752667/10000000) (δ := 9553/1000000000) (ψ := -55451/50000) 188 146
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t131 : ((104295247823/1250000000000 : ℚ) : ℝ) ≤ stT188 131 := by
  have hc : ((954971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104295247823/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((954971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c132 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-79627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4326829/10000000) (δ := 9553/1000000000) (ψ := -55451/50000) 188 146
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t132 : ((-17332056157/1250000000000 : ℚ) : ℝ) ≤ stT188 132 := by
  have hc : ((-19913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17332056157/1250000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-19913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c133 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-31249/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156679/200000) (δ := 4723/500000000) (ψ := -55451/50000) 188 147
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t133 : ((-43356280399/500000000000 : ℚ) : ℝ) ≤ stT188 133 := by
  have hc : ((-500009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43356280399/500000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-500009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c134 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-153927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33698/78125) (δ := 18957/1000000000) (ψ := -55451/50000) 188 147
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t134 : ((-133015957013/10000000000000 : ℚ) : ℝ) ≤ stT188 134 := by
  have hc : ((-153977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133015957013/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-153977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c135 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((236707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409459/5000000) (δ := 4723/500000000) (ψ := -55451/50000) 188 147
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t135 : ((203713961759/2500000000000 : ℚ) : ℝ) ≤ stT188 135 := by
  have hc : ((473389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203713961759/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((473389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c136 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((488967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2649729/10000000) (δ := 4723/500000000) (ψ := -55451/50000) 188 147
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t136 : ((104810604041/2500000000000 : ℚ) : ℝ) ≤ stT188 136 := by
  have hc : ((488917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104810604041/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((488917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c137 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-190501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1523249/2500000) (δ := 4723/500000000) (ψ := -55451/50000) 188 147
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t137 : ((-162766732833/2500000000000 : ℚ) : ℝ) ≤ stT188 137 := by
  have hc : ((-381027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162766732833/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-381027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c138 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-788227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3098399/5000000) (δ := 1183/125000000) (ψ := -55451/50000) 188 148
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t138 : ((-671026314189/10000000000000 : ℚ) : ℝ) ≤ stT188 138 := by
  have hc : ((-788277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-671026314189/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-788277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c139 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((434509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2803257/10000000) (δ := 1183/125000000) (ψ := -55451/50000) 188 148
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t139 : ((92125727573/2500000000000 : ℚ) : ℝ) ≤ stT188 139 := by
  have hc : ((434459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92125727573/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((434459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c140 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((487243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 282969/5000000) (δ := 1183/125000000) (ψ := -55451/50000) 188 148
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t140 : ((102943560393/1250000000000 : ℚ) : ℝ) ≤ stT188 140 := by
  have hc : ((243609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102943560393/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((243609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c141 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((127/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 977779/2500000) (δ := 1183/125000000) (ψ := -55451/50000) 188 148
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t141 : ((53055513/100000000000 : ℚ) : ℝ) ≤ stT188 141 := by
  have hc : ((63/10000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53055513/100000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((63/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c142 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-969279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72327/100000) (δ := 1183/125000000) (ψ := -55451/50000) 188 148
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t142 : ((-406721724439/5000000000000 : ℚ) : ℝ) ≤ stT188 142 := by
  have hc : ((-969329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406721724439/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-969329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c143 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-239713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5176991/10000000) (δ := 9571/1000000000) (ψ := -55451/50000) 188 149
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t143 : ((-100239612167/2500000000000 : ℚ) : ℝ) ≤ stT188 143 := by
  have hc : ((-119869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100239612167/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-119869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c144 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((362177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1901749/10000000) (δ := 9571/1000000000) (ψ := -55451/50000) 188 149
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t144 : ((37724151577/625000000000 : ℚ) : ℝ) ≤ stT188 144 := by
  have hc : ((45269/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37724151577/625000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((45269/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c145 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((428763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 675443/5000000) (δ := 9571/1000000000) (ψ := -55451/50000) 188 149
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t145 : ((89011796763/1250000000000 : ℚ) : ℝ) ≤ stT188 145 := by
  have hc : ((214369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89011796763/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((214369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c146 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-4042/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4581149/10000000) (δ := 9571/1000000000) (ψ := -55451/50000) 188 149
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t146 : ((-53533280307/2500000000000 : ℚ) : ℝ) ≤ stT188 146 := by
  have hc : ((-129369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53533280307/2500000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-129369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c147 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-499833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3894661/5000000) (δ := 9571/1000000000) (ψ := -55451/50000) 188 149
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t147 : ((-206138190123/2500000000000 : ℚ) : ℝ) ≤ stT188 147 := by
  have hc : ((-249929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206138190123/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-249929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c148 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-316537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4732183/10000000) (δ := 381/40000000) (ψ := -55451/50000) 188 150
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t148 : ((-52046586213/2000000000000 : ℚ) : ℝ) ≤ stT188 148 := by
  have hc : ((-316587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52046586213/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-316587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c149 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((50617/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -391789/2500000) (δ := 381/40000000) (ψ := -55451/50000) 188 150
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t149 : ((331715643441/5000000000000 : ℚ) : ℝ) ≤ stT188 149 := by
  have hc : ((404911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331715643441/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((404911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c150 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((201911/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1576627/10000000) (δ := 381/40000000) (ψ := -55451/50000) 188 150
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t150 : ((20606164707/312500000000 : ℚ) : ℝ) ≤ stT188 150 := by
  have hc : ((403797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20606164707/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((403797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c151 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-19009/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4699589/10000000) (δ := 381/40000000) (ψ := -55451/50000) 188 150
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t151 : ((-123774865533/5000000000000 : ℚ) : ℝ) ≤ stT188 151 := by
  have hc : ((-152097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123774865533/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-152097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c152 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-999783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3900959/5000000) (δ := 381/40000000) (ψ := -55451/50000) 188 150
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t152 : ((-202743136241/2500000000000 : ℚ) : ℝ) ≤ stT188 152 := by
  have hc : ((-999833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202743136241/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-999833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c153 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-351179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4824067/10000000) (δ := 9417/1000000000) (ψ := -55451/50000) 188 151
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t153 : ((-283952138737/10000000000000 : ℚ) : ℝ) ≤ stT188 153 := by
  have hc : ((-351229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283952138737/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-351229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c154 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((7617/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -881079/5000000) (δ := 9417/1000000000) (ψ := -55451/50000) 188 151
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t154 : ((6137543263/100000000000 : ℚ) : ℝ) ≤ stT188 154 := by
  have hc : ((15233/20000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6137543263/100000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((15233/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c155 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((871783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279917/10000000) (δ := 9417/1000000000) (ψ := -55451/50000) 188 151
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t155 : ((700192508527/10000000000000 : ℚ) : ℝ) ≤ stT188 155 := by
  have hc : ((871733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((700192508527/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((871733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c156 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-9351/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107561/250000) (δ := 9417/1000000000) (ψ := -55451/50000) 188 151
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t156 : ((-59914367953/5000000000000 : ℚ) : ℝ) ≤ stT188 156 := by
  have hc : ((-74833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59914367953/5000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-74833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c157 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-976043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3652823/5000000) (δ := 9417/1000000000) (ψ := -55451/50000) 188 151
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t157 : ((-779007134091/10000000000000 : ℚ) : ℝ) ≤ stT188 157 := by
  have hc : ((-976093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-779007134091/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-976093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c158 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-112347/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5418193/10000000) (δ := 9493/1000000000) (ψ := -55451/50000) 188 152
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t158 : ((-44693255103/1000000000000 : ℚ) : ℝ) ≤ stT188 158 := by
  have hc : ((-112357/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44693255103/1000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-112357/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c159 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((556069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2452869/10000000) (δ := 9493/1000000000) (ψ := -55451/50000) 188 152
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t159 : ((440951423969/10000000000000 : ℚ) : ℝ) ≤ stT188 159 := by
  have hc : ((556019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440951423969/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((556019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c160 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((980553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493843/10000000) (δ := 9493/1000000000) (ψ := -55451/50000) 188 152
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t160 : ((775155276207/10000000000000 : ℚ) : ℝ) ≤ stT188 160 := by
  have hc : ((980503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((775155276207/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((980503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c161 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((50139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1711089/5000000) (δ := 9493/1000000000) (ψ := -55451/50000) 188 152
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t161 : ((7901039183/500000000000 : ℚ) : ℝ) ≤ stT188 161 := by
  have hc : ((100253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7901039183/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((100253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c162 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-164087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3166209/5000000) (δ := 9493/1000000000) (ψ := -55451/50000) 188 152
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t162 : ((-5157076419/80000000000 : ℚ) : ℝ) ≤ stT188 162 := by
  have hc : ((-164097/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5157076419/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-164097/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c163 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-26669/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1620803/2500000) (δ := 3/312500) (ψ := -55451/50000) 188 153
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t163 : ((-334240183269/5000000000000 : ℚ) : ℝ) ≤ stT188 163 := by
  have hc : ((-426729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334240183269/5000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-426729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c164 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((127013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1804299/5000000) (δ := 3/312500) (ψ := -55451/50000) 188 153
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t164 : ((24785335971/2500000000000 : ℚ) : ℝ) ≤ stT188 164 := by
  have hc : ((126963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24785335971/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((126963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c165 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((955163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -187867/2500000) (δ := 3/312500) (ψ := -55451/50000) 188 153
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t165 : ((371776780137/5000000000000 : ℚ) : ℝ) ≤ stT188 165 := by
  have hc : ((955113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371776780137/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((955113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c166 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((670907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2088413/10000000) (δ := 3/312500) (ψ := -55451/50000) 188 153
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t166 : ((10413713211/200000000000 : ℚ) : ℝ) ≤ stT188 166 := by
  have hc : ((670857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10413713211/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((670857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c167 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-191811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61391/125000) (δ := 3/312500) (ψ := -55451/50000) 188 153
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t167 : ((-579872269/19531250000 : ℚ) : ℝ) ≤ stT188 167 := by
  have hc : ((-47959/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-579872269/19531250000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-47959/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c168 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-124813/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7717227/10000000) (δ := 3/312500) (ψ := -55451/50000) 188 153
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t168 : ((-385200693209/5000000000000 : ℚ) : ℝ) ≤ stT188 168 := by
  have hc : ((-499277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385200693209/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-499277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c169 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-121991/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5201381/10000000) (δ := 1187/125000000) (ψ := -55451/50000) 188 154
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t169 : ((-187697748617/5000000000000 : ℚ) : ℝ) ≤ stT188 169 := by
  have hc : ((-244007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187697748617/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-244007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c170 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((564137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1214261/5000000) (δ := 1187/125000000) (ψ := -55451/50000) 188 154
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t170 : ((108158605467/2500000000000 : ℚ) : ℝ) ≤ stT188 170 := by
  have hc : ((564087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108158605467/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((564087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c171 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((495701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13123/400000) (δ := 1187/125000000) (ψ := -55451/50000) 188 154
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t171 : ((94763213761/1250000000000 : ℚ) : ℝ) ≤ stT188 171 := by
  have hc : ((123919/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94763213761/1250000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((123919/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c172 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((6733/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1534299/5000000) (δ := 1187/125000000) (ψ := -55451/50000) 188 154
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t172 : ((320818509/12500000000 : ℚ) : ℝ) ≤ stT188 172 := by
  have hc : ((1683/5000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320818509/12500000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((1683/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c173 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-21221/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1158647/2000000) (δ := 1187/125000000) (ψ := -55451/50000) 188 154
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t173 : ((-129081737223/2500000000000 : ℚ) : ℝ) ≤ stT188 173 := by
  have hc : ((-339561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129081737223/2500000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-339561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c174 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-60411/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7205789/10000000) (δ := 4707/500000000) (ψ := -55451/50000) 188 155
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t174 : ((-366399101987/5000000000000 : ℚ) : ℝ) ≤ stT188 174 := by
  have hc : ((-483313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366399101987/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-483313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c175 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-116007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112809/250000) (δ := 4707/500000000) (ψ := -55451/50000) 188 155
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t175 : ((-1370499277/78125000000 : ℚ) : ℝ) ≤ stT188 175 := by
  have hc : ((-3626/15625 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1370499277/78125000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-3626/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c176 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((23209/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18343/100000) (δ := 4707/500000000) (ψ := -55451/50000) 188 155
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t176 : ((139946046591/2500000000000 : ℚ) : ℝ) ≤ stT188 176 := by
  have hc : ((371319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139946046591/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((371319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c177 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((945571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414313/5000000) (δ := 4707/500000000) (ψ := -55451/50000) 188 155
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t177 : ((355348538783/5000000000000 : ℚ) : ℝ) ≤ stT188 177 := by
  have hc : ((945521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355348538783/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((945521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c178 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((89609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108641/312500) (δ := 4707/500000000) (ψ := -55451/50000) 188 155
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t178 : ((4196624069/312500000000 : ℚ) : ℝ) ≤ stT188 178 := by
  have hc : ((5599/31250 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4196624069/312500000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((5599/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c179 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-383143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6109593/10000000) (δ := 4707/500000000) (ψ := -55451/50000) 188 155
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t179 : ((-1118724833/19531250000 : ℚ) : ℝ) ≤ stT188 179 := by
  have hc : ((-11974/15625 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1118724833/19531250000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-11974/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c180 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-117439/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -349/500) (δ := 4761/500000000) (ψ := -55451/50000) 188 156
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t180 : ((-87538521759/1250000000000 : ℚ) : ℝ) ≤ stT188 180 := by
  have hc : ((-469781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87538521759/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-469781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c181 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-178681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2188053/5000000) (δ := 4761/500000000) (ψ := -55451/50000) 188 156
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t181 : ((-26569971729/2000000000000 : ℚ) : ℝ) ≤ stT188 181 := by
  have hc : ((-178731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26569971729/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-178731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c182 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((755331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -893297/5000000) (δ := 4761/500000000) (ψ := -55451/50000) 188 156
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t182 : ((559851285969/10000000000000 : ℚ) : ℝ) ≤ stT188 182 := by
  have hc : ((755281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((559851285969/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((755281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c183 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((950639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 788771/10000000) (δ := 4761/500000000) (ψ := -55451/50000) 188 156
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t183 : ((702695351169/10000000000000 : ℚ) : ℝ) ≤ stT188 183 := by
  have hc : ((950589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((702695351169/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((950589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c184 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((2859/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3350083/10000000) (δ := 4761/500000000) (ψ := -55451/50000) 188 156
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t184 : ((16857758203/1000000000000 : ℚ) : ℝ) ≤ stT188 184 := by
  have hc : ((22867/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16857758203/1000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((22867/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c185 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-88637/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589753/1000000) (δ := 4761/500000000) (ψ := -55451/50000) 188 156
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t185 : ((-52137477639/1000000000000 : ℚ) : ℝ) ≤ stT188 185 := by
  have hc : ((-354573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52137477639/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-354573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c186 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-973463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3638379/5000000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t186 : ((-178453694517/2500000000000 : ℚ) : ℝ) ≤ stT188 186 := by
  have hc : ((-973513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178453694517/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-973513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c187 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-325793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2378309/5000000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t187 : ((-238280188139/10000000000000 : ℚ) : ℝ) ≤ stT188 187 := by
  have hc : ((-325843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238280188139/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-325843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c188 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((31081/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2249967/10000000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t188 : ((11333147967/250000000000 : ℚ) : ℝ) ≤ stT188 188 := by
  have hc : ((62157/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11333147967/250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((62157/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c189 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((995263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24343/1000000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t189 : ((22622186703/312500000000 : ℚ) : ℝ) ≤ stT188 189 := by
  have hc : ((995213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22622186703/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((995213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c190 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((18519/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136181/500000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t190 : ((3358409773/100000000000 : ℚ) : ℝ) ≤ stT188 190 := by
  have hc : ((18517/40000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3358409773/100000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((18517/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c191 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-484279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2595419/5000000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t191 : ((-14017934247/400000000000 : ℚ) : ℝ) ≤ stT188 191 := by
  have hc : ((-484329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14017934247/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-484329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c192 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-996513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7645131/10000000) (δ := 4787/500000000) (ψ := -55451/50000) 188 157
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t192 : ((-89900944793/1250000000000 : ℚ) : ℝ) ≤ stT188 192 := by
  have hc : ((-996563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89900944793/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-996563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c193 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-313507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1405319/2500000) (δ := 9467/1000000000) (ψ := -55451/50000) 188 158
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t193 : ((-7052667191/156250000000 : ℚ) : ℝ) ≤ stT188 193 := by
  have hc : ((-78383/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7052667191/156250000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-78383/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c194 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((144829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -798079/2500000) (δ := 9467/1000000000) (ψ := -55451/50000) 188 158
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t194 : ((12995398779/625000000000 : ℚ) : ℝ) ≤ stT188 194 := by
  have hc : ((36201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12995398779/625000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((36201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c195 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((952229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387929/5000000) (δ := 9467/1000000000) (ψ := -55451/50000) 188 158
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t195 : ((340934356203/5000000000000 : ℚ) : ℝ) ≤ stT188 195 := by
  have hc : ((952179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340934356203/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((952179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c196 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((795299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628239/10000000) (δ := 9467/1000000000) (ψ := -55451/50000) 188 158
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t196 : ((113606886393/2000000000000 : ℚ) : ℝ) ≤ stT188 196 := by
  have hc : ((795249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113606886393/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((795249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c197 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-37241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1005029/2500000) (δ := 9467/1000000000) (ψ := -55451/50000) 188 158
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t197 : ((-26568756061/10000000000000 : ℚ) : ℝ) ≤ stT188 197 := by
  have hc : ((-37291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26568756061/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-37291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c198 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-20889/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6399867/10000000) (δ := 9467/1000000000) (ψ := -55451/50000) 188 158
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t198 : ((-5938429587/100000000000 : ℚ) : ℝ) ≤ stT188 198 := by
  have hc : ((-83561/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5938429587/100000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-83561/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c199 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-933959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694033/1000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t199 : ((-331051083969/5000000000000 : ℚ) : ℝ) ≤ stT188 199 := by
  have hc : ((-934009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331051083969/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-934009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c200 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-51993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -916891/2000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t200 : ((-36771685321/2000000000000 : ℚ) : ℝ) ≤ stT188 200 := by
  have hc : ((-52003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36771685321/2000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-52003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c201 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((12493/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2240283/10000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t201 : ((440558487/10000000000 : ℚ) : ℝ) ≤ stT188 201 := by
  have hc : ((3123/5000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440558487/10000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((3123/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c202 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((24983/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46093/5000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t202 : ((70308337419/1000000000000 : ℚ) : ℝ) ≤ stT188 202 := by
  have hc : ((99927/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70308337419/1000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((99927/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c203 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((569191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2413187/10000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t203 : ((199729220271/5000000000000 : ℚ) : ℝ) ≤ stT188 203 := by
  have hc : ((569141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199729220271/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((569141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c204 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-156481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4722767/10000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t204 : ((-54788133673/2500000000000 : ℚ) : ℝ) ≤ stT188 204 := by
  have hc : ((-78253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54788133673/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-78253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c205 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-236253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7021067/10000000) (δ := 9443/1000000000) (ψ := -55451/50000) 188 159
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t205 : ((-330030298861/5000000000000 : ℚ) : ℝ) ≤ stT188 205 := by
  have hc : ((-472531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330030298861/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-472531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c206 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-835541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3199891/5000000) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t206 : ((-291092329897/5000000000000 : ℚ) : ℝ) ≤ stT188 206 := by
  have hc : ((-835591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291092329897/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-835591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c207 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-39313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51547/125000) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t207 : ((-13670918781/2500000000000 : ℚ) : ℝ) ≤ stT188 207 := by
  have hc : ((-19669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13670918781/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-19669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c208 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((736121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1858689/10000000) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t208 : ((4082985837/80000000000 : ℚ) : ℝ) ≤ stT188 208 := by
  have hc : ((736071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4082985837/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((736071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c209 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((987511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15821/400000) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t209 : ((341520299077/5000000000000 : ℚ) : ℝ) ≤ stT188 209 := by
  have hc : ((987461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341520299077/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((987461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c210 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((246357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20617/78125) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t210 : ((8499254579/250000000000 : ℚ) : ℝ) ≤ stT188 210 := by
  have hc : ((61583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8499254579/250000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((61583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c211 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-23061/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2435879/5000000) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t211 : ((-127024100077/5000000000000 : ℚ) : ℝ) ≤ stT188 211 := by
  have hc : ((-184513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127024100077/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-184513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c212 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-190829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1418793/2000000) (δ := 191/20000000) (ψ := -55451/50000) 188 160
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t212 : ((-131068797717/2000000000000 : ℚ) : ℝ) ≤ stT188 212 := by
  have hc : ((-190839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131068797717/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-190839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c213 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-418039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3201113/5000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t213 : ((-17903303381/312500000000 : ℚ) : ℝ) ≤ stT188 213 := by
  have hc : ((-26129/31250 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17903303381/312500000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-26129/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c214 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-54651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4200793/10000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t214 : ((-4671968517/625000000000 : ℚ) : ℝ) ≤ stT188 214 := by
  have hc : ((-13669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4671968517/625000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-13669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c215 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((173483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2009653/10000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t215 : ((118305840177/2500000000000 : ℚ) : ℝ) ≤ stT188 215 := by
  have hc : ((346941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118305840177/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((346941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c216 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((249413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34267/2000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t216 : ((339390684813/5000000000000 : ℚ) : ℝ) ≤ stT188 216 := by
  have hc : ((498801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339390684813/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((498801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c217 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((592299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1171109/5000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t217 : ((100511170039/2500000000000 : ℚ) : ℝ) ≤ stT188 217 := by
  have hc : ((592249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100511170039/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((592249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c218 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-28553/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4503137/10000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t218 : ((-38685560391/2500000000000 : ℚ) : ℝ) ≤ stT188 218 := by
  have hc : ((-114237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38685560391/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-114237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c219 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-887033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3327093/5000000) (δ := 4773/500000000) (ψ := -55451/50000) 188 161
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t219 : ((-299717846127/5000000000000 : ℚ) : ℝ) ≤ stT188 219 := by
  have hc : ((-887083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299717846127/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-887083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c220 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-929931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6912551/10000000) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t220 : ((-3134965951/50000000000 : ℚ) : ℝ) ≤ stT188 220 := by
  have hc : ((-929981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3134965951/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-929981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c221 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-335001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4781007/10000000) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t221 : ((-225379761323/10000000000000 : ℚ) : ℝ) ≤ stT188 221 := by
  have hc : ((-335051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225379761323/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-335051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c222 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((242839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -531829/2000000) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t222 : ((20370759123/625000000000 : ℚ) : ℝ) ≤ stT188 222 := by
  have hc : ((121407/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20370759123/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((121407/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c223 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((488089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -546777/10000000) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t223 : ((2553371637/39062500000 : ℚ) : ℝ) ≤ stT188 223 := by
  have hc : ((15252/15625 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2553371637/39062500000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((15252/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c224 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((25389/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97259/625000) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t224 : ((271403080447/5000000000000 : ℚ) : ℝ) ≤ stT188 224 := by
  have hc : ((406199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271403080447/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((406199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c225 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((27671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228107/625000) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t225 : ((18438981561/2500000000000 : ℚ) : ℝ) ≤ stT188 225 := by
  have hc : ((55317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18438981561/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((55317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c226 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-26459/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5733951/10000000) (δ := 3793/200000000) (ψ := -55451/50000) 188 162
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t226 : ((-17601619051/400000000000 : ℚ) : ℝ) ≤ stT188 226 := by
  have hc : ((-26461/40000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17601619051/400000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-26461/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c227 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-499919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61008/78125) (δ := 4719/500000000) (ψ := -55451/50000) 188 162
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t227 : ((-10369525983/156250000000 : ℚ) : ℝ) ≤ stT188 227 := by
  have hc : ((-62493/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10369525983/156250000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-62493/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c228 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-86333/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5833007/10000000) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t228 : ((-228718544319/5000000000000 : ℚ) : ℝ) ≤ stT188 228 := by
  have hc : ((-345357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228718544319/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-345357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c229 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((377/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3776099/10000000) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t229 : ((1991375043/500000000000 : ℚ) : ℝ) ≤ stT188 229 := by
  have hc : ((6027/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1991375043/500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((6027/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c230 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((770439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -216021/1250000) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t230 : ((25398954941/500000000000 : ℚ) : ℝ) ≤ stT188 230 := by
  have hc : ((770389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25398954941/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((770389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c231 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((496139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1943/62500) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t231 : ((163209351207/2500000000000 : ℚ) : ℝ) ≤ stT188 231 := by
  have hc : ((248057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163209351207/2500000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((248057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c232 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((296331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 585273/2500000) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t232 : ((24316796349/625000000000 : ℚ) : ℝ) ≤ stT188 232 := by
  have hc : ((148153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24316796349/625000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((148153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c233 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-173367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4362609/10000000) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t233 : ((-56804645937/5000000000000 : ℚ) : ℝ) ≤ stT188 233 := by
  have hc : ((-173417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56804645937/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-173417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c234 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-10377/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3187739/5000000) (δ := 37/3906250) (ψ := -55451/50000) 188 163
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t234 : ((-54272571141/1000000000000 : ℚ) : ℝ) ≤ stT188 234 := by
  have hc : ((-83021/100000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54272571141/1000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-83021/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c235 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-977967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7328217/10000000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t235 : ((-637988851593/10000000000000 : ℚ) : ℝ) ≤ stT188 235 := by
  have hc : ((-978017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-637988851593/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-978017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c236 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-533037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -666557/1250000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t236 : ((-69402063443/2000000000000 : ℚ) : ℝ) ≤ stT188 236 := by
  have hc : ((-533087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69402063443/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-533087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c237 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((230639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669031/2000000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t237 : ((149783466141/10000000000000 : ℚ) : ℝ) ≤ stT188 237 := by
  have hc : ((230589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149783466141/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((230589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c238 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((170871/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68311/500000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t238 : ((110752612783/2000000000000 : ℚ) : ℝ) ≤ stT188 238 := by
  have hc : ((170861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110752612783/2000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((170861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c239 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((485457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604443/10000000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t239 : ((19624984217/312500000000 : ℚ) : ℝ) ≤ stT188 239 := by
  have hc : ((60679/62500 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19624984217/312500000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((60679/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c240 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((647/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2566881/10000000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t240 : ((6681539447/200000000000 : ℚ) : ℝ) ≤ stT188 240 := by
  have hc : ((10351/20000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6681539447/200000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((10351/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c241 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-235429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4521141/10000000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t241 : ((-151685446203/10000000000000 : ℚ) : ℝ) ≤ stT188 241 := by
  have hc : ((-235479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151685446203/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-235479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c242 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-212519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6467317/10000000) (δ := 9579/1000000000) (ψ := -55451/50000) 188 164
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t242 : ((-10929644919/200000000000 : ℚ) : ℝ) ≤ stT188 242 := by
  have hc : ((-425063/500000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10929644919/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-425063/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c243 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-975769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1825627/2500000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t243 : ((-625988864319/10000000000000 : ℚ) : ℝ) ≤ stT188 243 := by
  have hc : ((-975819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625988864319/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-975819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c244 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-273229/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671539/1250000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t244 : ((-17493311199/500000000000 : ℚ) : ℝ) ≤ stT188 244 := by
  have hc : ((-136627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17493311199/500000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-136627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c245 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((189627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690007/2000000) (δ := 9443/500000000) (ψ := -55451/50000) 188 165
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t245 : ((30279048863/2500000000000 : ℚ) : ℝ) ≤ stT188 245 := by
  have hc : ((189577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30279048863/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((189577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c246 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((817221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1535561/10000000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t246 : ((65126077187/1250000000000 : ℚ) : ℝ) ≤ stT188 246 := by
  have hc : ((817171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65126077187/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((817171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c247 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((989001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74227/2000000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t247 : ((157313424521/2500000000000 : ℚ) : ℝ) ≤ stT188 247 := by
  have hc : ((988951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157313424521/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((988951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c248 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((123057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2270123/10000000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t248 : ((15626969/400000000 : ℚ) : ℝ) ≤ stT188 248 := by
  have hc : ((123047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15626969/400000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((123047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c249 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-46823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83229/200000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t249 : ((-4638867/781250000 : ℚ) : ℝ) ≤ stT188 249 := by
  have hc : ((-1464/15625 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4638867/781250000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-1464/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_c250 :
    |Real.cos (((188 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((-1499/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6045257/10000000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st188_t250 : ((-1185143487/25000000000 : ℚ) : ℝ) ≤ stT188 250 := by
  have hc : ((-14991/20000 : ℚ) : ℝ)
      ≤ Real.cos (((188 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st188_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1185143487/25000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-14991/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st188_p1 : ((445489/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT188 (i+1) := by
  rw [Finset.sum_range_one]
  exact st188_t1

theorem st188_p2 : ((2642253840189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT188 (i+1))
      = (∑ i ∈ Finset.range 1, stT188 (i+1)) + stT188 2 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 1
    simpa using h
  have hprev := st188_p1
  have hstep := st188_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p3 : ((8039602627521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT188 (i+1))
      = (∑ i ∈ Finset.range 2, stT188 (i+1)) + stT188 3 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 2
    simpa using h
  have hprev := st188_p2
  have hstep := st188_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p4 : ((13294539698109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT188 (i+1))
      = (∑ i ∈ Finset.range 3, stT188 (i+1)) + stT188 4 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 3
    simpa using h
  have hprev := st188_p3
  have hstep := st188_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p5 : ((11073507019341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT188 (i+1))
      = (∑ i ∈ Finset.range 4, stT188 (i+1)) + stT188 5 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 4
    simpa using h
  have hprev := st188_p4
  have hstep := st188_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p6 : ((12038111783819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT188 (i+1))
      = (∑ i ∈ Finset.range 5, stT188 (i+1)) + stT188 6 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 5
    simpa using h
  have hprev := st188_p5
  have hstep := st188_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p7 : ((1121931762673/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT188 (i+1))
      = (∑ i ∈ Finset.range 6, stT188 (i+1)) + stT188 7 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 6
    simpa using h
  have hprev := st188_p6
  have hstep := st188_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p8 : ((3085769379303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT188 (i+1))
      = (∑ i ∈ Finset.range 7, stT188 (i+1)) + stT188 8 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 7
    simpa using h
  have hprev := st188_p7
  have hstep := st188_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p9 : ((363673938663/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT188 (i+1))
      = (∑ i ∈ Finset.range 8, stT188 (i+1)) + stT188 9 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 8
    simpa using h
  have hprev := st188_p8
  have hstep := st188_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p10 : ((2982982637469/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT188 (i+1))
      = (∑ i ∈ Finset.range 9, stT188 (i+1)) + stT188 10 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 9
    simpa using h
  have hprev := st188_p9
  have hstep := st188_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p11 : ((1461169665179/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT188 (i+1))
      = (∑ i ∈ Finset.range 10, stT188 (i+1)) + stT188 11 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 10
    simpa using h
  have hprev := st188_p10
  have hstep := st188_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p12 : ((5884235549223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT188 (i+1))
      = (∑ i ∈ Finset.range 11, stT188 (i+1)) + stT188 12 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 11
    simpa using h
  have hprev := st188_p11
  have hstep := st188_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p13 : ((7110490037973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT188 (i+1))
      = (∑ i ∈ Finset.range 12, stT188 (i+1)) + stT188 13 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 12
    simpa using h
  have hprev := st188_p12
  have hstep := st188_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p14 : ((7961684888629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT188 (i+1))
      = (∑ i ∈ Finset.range 13, stT188 (i+1)) + stT188 14 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 13
    simpa using h
  have hprev := st188_p13
  have hstep := st188_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p15 : ((8326251266277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT188 (i+1))
      = (∑ i ∈ Finset.range 14, stT188 (i+1)) + stT188 15 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 14
    simpa using h
  have hprev := st188_p14
  have hstep := st188_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p16 : ((9149923766277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT188 (i+1))
      = (∑ i ∈ Finset.range 15, stT188 (i+1)) + stT188 16 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 15
    simpa using h
  have hprev := st188_p15
  have hstep := st188_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p17 : ((2060376838299/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT188 (i+1))
      = (∑ i ∈ Finset.range 16, stT188 (i+1)) + stT188 17 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 16
    simpa using h
  have hprev := st188_p16
  have hstep := st188_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p18 : ((154694853883/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT188 (i+1))
      = (∑ i ∈ Finset.range 17, stT188 (i+1)) + stT188 18 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 17
    simpa using h
  have hprev := st188_p17
  have hstep := st188_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p19 : ((18943096632887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT188 (i+1))
      = (∑ i ∈ Finset.range 18, stT188 (i+1)) + stT188 19 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 18
    simpa using h
  have hprev := st188_p18
  have hstep := st188_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p20 : ((19794769831847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT188 (i+1))
      = (∑ i ∈ Finset.range 19, stT188 (i+1)) + stT188 20 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 19
    simpa using h
  have hprev := st188_p19
  have hstep := st188_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p21 : ((3898643776039/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT188 (i+1))
      = (∑ i ∈ Finset.range 20, stT188 (i+1)) + stT188 21 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 20
    simpa using h
  have hprev := st188_p20
  have hstep := st188_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p22 : ((3679234568743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT188 (i+1))
      = (∑ i ∈ Finset.range 21, stT188 (i+1)) + stT188 22 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 21
    simpa using h
  have hprev := st188_p21
  have hstep := st188_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p23 : ((20479748815427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT188 (i+1))
      = (∑ i ∈ Finset.range 22, stT188 (i+1)) + stT188 23 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 22
    simpa using h
  have hprev := st188_p22
  have hstep := st188_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p24 : ((20256083805761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT188 (i+1))
      = (∑ i ∈ Finset.range 23, stT188 (i+1)) + stT188 24 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 23
    simpa using h
  have hprev := st188_p23
  have hstep := st188_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p25 : ((18260838808139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT188 (i+1))
      = (∑ i ∈ Finset.range 24, stT188 (i+1)) + stT188 25 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 24
    simpa using h
  have hprev := st188_p24
  have hstep := st188_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p26 : ((17235345237177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT188 (i+1))
      = (∑ i ∈ Finset.range 25, stT188 (i+1)) + stT188 26 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 25
    simpa using h
  have hprev := st188_p25
  have hstep := st188_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p27 : ((17733344253177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT188 (i+1))
      = (∑ i ∈ Finset.range 26, stT188 (i+1)) + stT188 27 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 26
    simpa using h
  have hprev := st188_p26
  have hstep := st188_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p28 : ((764379295857/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT188 (i+1))
      = (∑ i ∈ Finset.range 27, stT188 (i+1)) + stT188 28 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 27
    simpa using h
  have hprev := st188_p27
  have hstep := st188_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p29 : ((5197154787001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT188 (i+1))
      = (∑ i ∈ Finset.range 28, stT188 (i+1)) + stT188 29 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 28
    simpa using h
  have hprev := st188_p28
  have hstep := st188_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p30 : ((22503090362759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT188 (i+1))
      = (∑ i ∈ Finset.range 29, stT188 (i+1)) + stT188 30 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 29
    simpa using h
  have hprev := st188_p29
  have hstep := st188_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p31 : ((6026185095523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT188 (i+1))
      = (∑ i ∈ Finset.range 30, stT188 (i+1)) + stT188 31 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 30
    simpa using h
  have hprev := st188_p30
  have hstep := st188_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p32 : ((6339132710503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT188 (i+1))
      = (∑ i ∈ Finset.range 31, stT188 (i+1)) + stT188 32 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 31
    simpa using h
  have hprev := st188_p31
  have hstep := st188_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p33 : ((6463045933317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT188 (i+1))
      = (∑ i ∈ Finset.range 32, stT188 (i+1)) + stT188 33 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 32
    simpa using h
  have hprev := st188_p32
  have hstep := st188_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p34 : ((12606361024203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT188 (i+1))
      = (∑ i ∈ Finset.range 33, stT188 (i+1)) + stT188 34 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 33
    simpa using h
  have hprev := st188_p33
  have hstep := st188_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p35 : ((23627852833517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT188 (i+1))
      = (∑ i ∈ Finset.range 34, stT188 (i+1)) + stT188 35 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 34
    simpa using h
  have hprev := st188_p34
  have hstep := st188_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p36 : ((11141432115593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT188 (i+1))
      = (∑ i ∈ Finset.range 35, stT188 (i+1)) + stT188 36 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 35
    simpa using h
  have hprev := st188_p35
  have hstep := st188_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p37 : ((22598452579571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT188 (i+1))
      = (∑ i ∈ Finset.range 36, stT188 (i+1)) + stT188 37 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 36
    simpa using h
  have hprev := st188_p36
  have hstep := st188_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p38 : ((24211131205679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT188 (i+1))
      = (∑ i ∈ Finset.range 37, stT188 (i+1)) + stT188 38 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 37
    simpa using h
  have hprev := st188_p37
  have hstep := st188_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p39 : ((986082781981/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT188 (i+1))
      = (∑ i ∈ Finset.range 38, stT188 (i+1)) + stT188 39 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 38
    simpa using h
  have hprev := st188_p38
  have hstep := st188_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p40 : ((5788580350381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT188 (i+1))
      = (∑ i ∈ Finset.range 39, stT188 (i+1)) + stT188 40 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 39
    simpa using h
  have hprev := st188_p39
  have hstep := st188_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p41 : ((5689622383749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT188 (i+1))
      = (∑ i ∈ Finset.range 40, stT188 (i+1)) + stT188 41 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 40
    simpa using h
  have hprev := st188_p40
  have hstep := st188_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p42 : ((24297203585629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT188 (i+1))
      = (∑ i ∈ Finset.range 41, stT188 (i+1)) + stT188 42 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 41
    simpa using h
  have hprev := st188_p41
  have hstep := st188_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p43 : ((4794505593257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT188 (i+1))
      = (∑ i ∈ Finset.range 42, stT188 (i+1)) + stT188 43 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 42
    simpa using h
  have hprev := st188_p42
  have hstep := st188_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p44 : ((710386307147/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT188 (i+1))
      = (∑ i ∈ Finset.range 43, stT188 (i+1)) + stT188 44 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 43
    simpa using h
  have hprev := st188_p43
  have hstep := st188_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p45 : ((2405561529923/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT188 (i+1))
      = (∑ i ∈ Finset.range 44, stT188 (i+1)) + stT188 45 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 44
    simpa using h
  have hprev := st188_p44
  have hstep := st188_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p46 : ((95622112759/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT188 (i+1))
      = (∑ i ∈ Finset.range 45, stT188 (i+1)) + stT188 46 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 45
    simpa using h
  have hprev := st188_p45
  have hstep := st188_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p47 : ((228594179587/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT188 (i+1))
      = (∑ i ∈ Finset.range 46, stT188 (i+1)) + stT188 47 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 46
    simpa using h
  have hprev := st188_p46
  have hstep := st188_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p48 : ((972049537753/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT188 (i+1))
      = (∑ i ∈ Finset.range 47, stT188 (i+1)) + stT188 48 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 47
    simpa using h
  have hprev := st188_p47
  have hstep := st188_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p49 : ((23285715180473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT188 (i+1))
      = (∑ i ∈ Finset.range 48, stT188 (i+1)) + stT188 49 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 48
    simpa using h
  have hprev := st188_p48
  have hstep := st188_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p50 : ((23474755860609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT188 (i+1))
      = (∑ i ∈ Finset.range 49, stT188 (i+1)) + stT188 50 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 49
    simpa using h
  have hprev := st188_p49
  have hstep := st188_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p51 : ((24080192123649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT188 (i+1))
      = (∑ i ∈ Finset.range 50, stT188 (i+1)) + stT188 51 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 50
    simpa using h
  have hprev := st188_p50
  have hstep := st188_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p52 : ((22947152766103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT188 (i+1))
      = (∑ i ∈ Finset.range 51, stT188 (i+1)) + stT188 52 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 51
    simpa using h
  have hprev := st188_p51
  have hstep := st188_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p53 : ((12149837151479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT188 (i+1))
      = (∑ i ∈ Finset.range 52, stT188 (i+1)) + stT188 53 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 52
    simpa using h
  have hprev := st188_p52
  have hstep := st188_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p54 : ((11482600049003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT188 (i+1))
      = (∑ i ∈ Finset.range 53, stT188 (i+1)) + stT188 54 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 53
    simpa using h
  have hprev := st188_p53
  have hstep := st188_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p55 : ((12072473372341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT188 (i+1))
      = (∑ i ∈ Finset.range 54, stT188 (i+1)) + stT188 55 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 54
    simpa using h
  have hprev := st188_p54
  have hstep := st188_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p56 : ((11584152050559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT188 (i+1))
      = (∑ i ∈ Finset.range 55, stT188 (i+1)) + stT188 56 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 55
    simpa using h
  have hprev := st188_p55
  have hstep := st188_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p57 : ((11976193654579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT188 (i+1))
      = (∑ i ∈ Finset.range 56, stT188 (i+1)) + stT188 57 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 56
    simpa using h
  have hprev := st188_p56
  have hstep := st188_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p58 : ((23316479121113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT188 (i+1))
      = (∑ i ∈ Finset.range 57, stT188 (i+1)) + stT188 58 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 57
    simpa using h
  have hprev := st188_p57
  have hstep := st188_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p59 : ((11931543165493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT188 (i+1))
      = (∑ i ∈ Finset.range 58, stT188 (i+1)) + stT188 59 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 58
    simpa using h
  have hprev := st188_p58
  have hstep := st188_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p60 : ((11671133982053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT188 (i+1))
      = (∑ i ∈ Finset.range 59, stT188 (i+1)) + stT188 60 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 59
    simpa using h
  have hprev := st188_p59
  have hstep := st188_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p61 : ((11949147968101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT188 (i+1))
      = (∑ i ∈ Finset.range 60, stT188 (i+1)) + stT188 61 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 60
    simpa using h
  have hprev := st188_p60
  have hstep := st188_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p62 : ((11625965479153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT188 (i+1))
      = (∑ i ∈ Finset.range 61, stT188 (i+1)) + stT188 62 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 61
    simpa using h
  have hprev := st188_p61
  have hstep := st188_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p63 : ((24031687687659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT188 (i+1))
      = (∑ i ∈ Finset.range 62, stT188 (i+1)) + stT188 63 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 62
    simpa using h
  have hprev := st188_p62
  have hstep := st188_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p64 : ((23093899437429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT188 (i+1))
      = (∑ i ∈ Finset.range 63, stT188 (i+1)) + stT188 64 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 63
    simpa using h
  have hprev := st188_p63
  have hstep := st188_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p65 : ((6046228715091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT188 (i+1))
      = (∑ i ∈ Finset.range 64, stT188 (i+1)) + stT188 65 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 64
    simpa using h
  have hprev := st188_p64
  have hstep := st188_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p66 : ((22984788737259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT188 (i+1))
      = (∑ i ∈ Finset.range 65, stT188 (i+1)) + stT188 66 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 65
    simpa using h
  have hprev := st188_p65
  have hstep := st188_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p67 : ((24201465240001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT188 (i+1))
      = (∑ i ∈ Finset.range 66, stT188 (i+1)) + stT188 67 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 66
    simpa using h
  have hprev := st188_p66
  have hstep := st188_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p68 : ((2310759361431/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT188 (i+1))
      = (∑ i ∈ Finset.range 67, stT188 (i+1)) + stT188 68 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 67
    simpa using h
  have hprev := st188_p67
  have hstep := st188_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p69 : ((1195396823529/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT188 (i+1))
      = (∑ i ∈ Finset.range 68, stT188 (i+1)) + stT188 69 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 68
    simpa using h
  have hprev := st188_p68
  have hstep := st188_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p70 : ((4713037325279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT188 (i+1))
      = (∑ i ∈ Finset.range 69, stT188 (i+1)) + stT188 70 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 69
    simpa using h
  have hprev := st188_p69
  have hstep := st188_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p71 : ((23347883281849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT188 (i+1))
      = (∑ i ∈ Finset.range 70, stT188 (i+1)) + stT188 71 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 70
    simpa using h
  have hprev := st188_p70
  have hstep := st188_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p72 : ((24103664743171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT188 (i+1))
      = (∑ i ∈ Finset.range 71, stT188 (i+1)) + stT188 72 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 71
    simpa using h
  have hprev := st188_p71
  have hstep := st188_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p73 : ((22994870253323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT188 (i+1))
      = (∑ i ∈ Finset.range 72, stT188 (i+1)) + stT188 73 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 72
    simpa using h
  have hprev := st188_p72
  have hstep := st188_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p74 : ((24118914796763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT188 (i+1))
      = (∑ i ∈ Finset.range 73, stT188 (i+1)) + stT188 74 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 73
    simpa using h
  have hprev := st188_p73
  have hstep := st188_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p75 : ((23379321878057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT188 (i+1))
      = (∑ i ∈ Finset.range 74, stT188 (i+1)) + stT188 75 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 74
    simpa using h
  have hprev := st188_p74
  have hstep := st188_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p76 : ((23429257624631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT188 (i+1))
      = (∑ i ∈ Finset.range 75, stT188 (i+1)) + stT188 76 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 75
    simpa using h
  have hprev := st188_p75
  have hstep := st188_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p77 : ((24110171612131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT188 (i+1))
      = (∑ i ∈ Finset.range 76, stT188 (i+1)) + stT188 77 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 76
    simpa using h
  have hprev := st188_p76
  have hstep := st188_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p78 : ((23003810323273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT188 (i+1))
      = (∑ i ∈ Finset.range 77, stT188 (i+1)) + stT188 78 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 77
    simpa using h
  have hprev := st188_p77
  have hstep := st188_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p79 : ((23973313542391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT188 (i+1))
      = (∑ i ∈ Finset.range 78, stT188 (i+1)) + stT188 79 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 78
    simpa using h
  have hprev := st188_p78
  have hstep := st188_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p80 : ((23683717021609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT188 (i+1))
      = (∑ i ∈ Finset.range 79, stT188 (i+1)) + stT188 80 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 79
    simpa using h
  have hprev := st188_p79
  have hstep := st188_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p81 : ((4621679534493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT188 (i+1))
      = (∑ i ∈ Finset.range 80, stT188 (i+1)) + stT188 81 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 80
    simpa using h
  have hprev := st188_p80
  have hstep := st188_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p82 : ((1209620602491/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT188 (i+1))
      = (∑ i ∈ Finset.range 81, stT188 (i+1)) + stT188 82 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 81
    simpa using h
  have hprev := st188_p81
  have hstep := st188_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p83 : ((5833169146053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT188 (i+1))
      = (∑ i ∈ Finset.range 82, stT188 (i+1)) + stT188 83 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 82
    simpa using h
  have hprev := st188_p82
  have hstep := st188_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p84 : ((23343237234643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT188 (i+1))
      = (∑ i ∈ Finset.range 83, stT188 (i+1)) + stT188 84 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 83
    simpa using h
  have hprev := st188_p83
  have hstep := st188_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p85 : ((4839502046899/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT188 (i+1))
      = (∑ i ∈ Finset.range 84, stT188 (i+1)) + stT188 85 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 84
    simpa using h
  have hprev := st188_p84
  have hstep := st188_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p86 : ((23160806773623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT188 (i+1))
      = (∑ i ∈ Finset.range 85, stT188 (i+1)) + stT188 86 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 85
    simpa using h
  have hprev := st188_p85
  have hstep := st188_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p87 : ((23501784490439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT188 (i+1))
      = (∑ i ∈ Finset.range 86, stT188 (i+1)) + stT188 87 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 86
    simpa using h
  have hprev := st188_p86
  have hstep := st188_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p88 : ((1510193864847/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT188 (i+1))
      = (∑ i ∈ Finset.range 87, stT188 (i+1)) + stT188 88 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 87
    simpa using h
  have hprev := st188_p87
  have hstep := st188_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p89 : ((2888768308033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT188 (i+1))
      = (∑ i ∈ Finset.range 88, stT188 (i+1)) + stT188 89 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 88
    simpa using h
  have hprev := st188_p88
  have hstep := st188_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p90 : ((5883535317017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT188 (i+1))
      = (∑ i ∈ Finset.range 89, stT188 (i+1)) + stT188 90 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 89
    simpa using h
  have hprev := st188_p89
  have hstep := st188_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p91 : ((1510541788847/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT188 (i+1))
      = (∑ i ∈ Finset.range 90, stT188 (i+1)) + stT188 91 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 90
    simpa using h
  have hprev := st188_p90
  have hstep := st188_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p92 : ((23140434128021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT188 (i+1))
      = (∑ i ∈ Finset.range 91, stT188 (i+1)) + stT188 92 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 91
    simpa using h
  have hprev := st188_p91
  have hstep := st188_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p93 : ((23442174425609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT188 (i+1))
      = (∑ i ∈ Finset.range 92, stT188 (i+1)) + stT188 93 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 92
    simpa using h
  have hprev := st188_p92
  have hstep := st188_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p94 : ((4841420611231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT188 (i+1))
      = (∑ i ∈ Finset.range 93, stT188 (i+1)) + stT188 94 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 93
    simpa using h
  have hprev := st188_p93
  have hstep := st188_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p95 : ((23268960170303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT188 (i+1))
      = (∑ i ∈ Finset.range 94, stT188 (i+1)) + stT188 95 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 94
    simpa using h
  have hprev := st188_p94
  have hstep := st188_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p96 : ((5812349481899/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT188 (i+1))
      = (∑ i ∈ Finset.range 95, stT188 (i+1)) + stT188 96 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 95
    simpa using h
  have hprev := st188_p95
  have hstep := st188_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p97 : ((12100107821629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT188 (i+1))
      = (∑ i ∈ Finset.range 96, stT188 (i+1)) + stT188 97 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 96
    simpa using h
  have hprev := st188_p96
  have hstep := st188_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p98 : ((23537344153281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT188 (i+1))
      = (∑ i ∈ Finset.range 97, stT188 (i+1)) + stT188 98 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 97
    simpa using h
  have hprev := st188_p97
  have hstep := st188_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p99 : ((23040333766559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT188 (i+1))
      = (∑ i ∈ Finset.range 98, stT188 (i+1)) + stT188 99 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 98
    simpa using h
  have hprev := st188_p98
  have hstep := st188_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p100 : ((12010316893129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT188 (i+1))
      = (∑ i ∈ Finset.range 99, stT188 (i+1)) + stT188 100 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 99
    simpa using h
  have hprev := st188_p99
  have hstep := st188_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p101 : ((11959971950481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT188 (i+1))
      = (∑ i ∈ Finset.range 100, stT188 (i+1)) + stT188 101 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 100
    simpa using h
  have hprev := st188_p100
  have hstep := st188_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p102 : ((11500696256347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT188 (i+1))
      = (∑ i ∈ Finset.range 101, stT188 (i+1)) + stT188 102 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 101
    simpa using h
  have hprev := st188_p101
  have hstep := st188_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p103 : ((11797294079953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT188 (i+1))
      = (∑ i ∈ Finset.range 102, stT188 (i+1)) + stT188 103 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 102
    simpa using h
  have hprev := st188_p102
  have hstep := st188_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p104 : ((12105199631983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT188 (i+1))
      = (∑ i ∈ Finset.range 103, stT188 (i+1)) + stT188 104 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 103
    simpa using h
  have hprev := st188_p103
  have hstep := st188_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p105 : ((2333193612341/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT188 (i+1))
      = (∑ i ∈ Finset.range 104, stT188 (i+1)) + stT188 105 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 104
    simpa using h
  have hprev := st188_p104
  have hstep := st188_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p106 : ((2310140139131/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT188 (i+1))
      = (∑ i ∈ Finset.range 105, stT188 (i+1)) + stT188 106 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 105
    simpa using h
  have hprev := st188_p105
  have hstep := st188_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p107 : ((12033552941999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT188 (i+1))
      = (∑ i ∈ Finset.range 106, stT188 (i+1)) + stT188 107 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 106
    simpa using h
  have hprev := st188_p106
  have hstep := st188_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p108 : ((5984874482471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT188 (i+1))
      = (∑ i ∈ Finset.range 107, stT188 (i+1)) + stT188 108 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 107
    simpa using h
  have hprev := st188_p107
  have hstep := st188_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p109 : ((4604593145067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT188 (i+1))
      = (∑ i ∈ Finset.range 108, stT188 (i+1)) + stT188 109 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 108
    simpa using h
  have hprev := st188_p108
  have hstep := st188_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p110 : ((23429892818853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT188 (i+1))
      = (∑ i ∈ Finset.range 109, stT188 (i+1)) + stT188 110 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 109
    simpa using h
  have hprev := st188_p109
  have hstep := st188_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p111 : ((24228131957539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT188 (i+1))
      = (∑ i ∈ Finset.range 110, stT188 (i+1)) + stT188 111 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 110
    simpa using h
  have hprev := st188_p110
  have hstep := st188_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p112 : ((4725778100023/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT188 (i+1))
      = (∑ i ∈ Finset.range 111, stT188 (i+1)) + stT188 112 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 111
    simpa using h
  have hprev := st188_p111
  have hstep := st188_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p113 : ((5741215706781/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT188 (i+1))
      = (∑ i ∈ Finset.range 112, stT188 (i+1)) + stT188 113 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 112
    simpa using h
  have hprev := st188_p112
  have hstep := st188_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p114 : ((23682370293189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT188 (i+1))
      = (∑ i ∈ Finset.range 113, stT188 (i+1)) + stT188 114 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 113
    simpa using h
  have hprev := st188_p113
  have hstep := st188_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p115 : ((24229323986861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT188 (i+1))
      = (∑ i ∈ Finset.range 114, stT188 (i+1)) + stT188 115 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 114
    simpa using h
  have hprev := st188_p114
  have hstep := st188_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p116 : ((23447561208493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT188 (i+1))
      = (∑ i ∈ Finset.range 115, stT188 (i+1)) + stT188 116 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 115
    simpa using h
  have hprev := st188_p115
  have hstep := st188_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p117 : ((11491280159009/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT188 (i+1))
      = (∑ i ∈ Finset.range 116, stT188 (i+1)) + stT188 117 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 116
    simpa using h
  have hprev := st188_p116
  have hstep := st188_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p118 : ((11895689237783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT188 (i+1))
      = (∑ i ∈ Finset.range 117, stT188 (i+1)) + stT188 118 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 117
    simpa using h
  have hprev := st188_p117
  have hstep := st188_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p119 : ((3027040489643/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT188 (i+1))
      = (∑ i ∈ Finset.range 118, stT188 (i+1)) + stT188 119 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 118
    simpa using h
  have hprev := st188_p118
  have hstep := st188_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p120 : ((4681281484279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT188 (i+1))
      = (∑ i ∈ Finset.range 119, stT188 (i+1)) + stT188 120 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 119
    simpa using h
  have hprev := st188_p119
  have hstep := st188_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p121 : ((22978323742223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT188 (i+1))
      = (∑ i ∈ Finset.range 120, stT188 (i+1)) + stT188 121 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 120
    simpa using h
  have hprev := st188_p120
  have hstep := st188_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p122 : ((11883390070513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT188 (i+1))
      = (∑ i ∈ Finset.range 121, stT188 (i+1)) + stT188 122 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 121
    simpa using h
  have hprev := st188_p121
  have hstep := st188_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p123 : ((24237874241787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT188 (i+1))
      = (∑ i ∈ Finset.range 122, stT188 (i+1)) + stT188 123 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 122
    simpa using h
  have hprev := st188_p122
  have hstep := st188_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p124 : ((23495807590877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT188 (i+1))
      = (∑ i ∈ Finset.range 123, stT188 (i+1)) + stT188 124 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 123
    simpa using h
  have hprev := st188_p123
  have hstep := st188_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p125 : ((22948033050837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT188 (i+1))
      = (∑ i ∈ Finset.range 124, stT188 (i+1)) + stT188 125 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 124
    simpa using h
  have hprev := st188_p124
  have hstep := st188_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p126 : ((23610745898617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT188 (i+1))
      = (∑ i ∈ Finset.range 125, stT188 (i+1)) + stT188 126 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 125
    simpa using h
  have hprev := st188_p125
  have hstep := st188_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p127 : ((24257353342257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT188 (i+1))
      = (∑ i ∈ Finset.range 126, stT188 (i+1)) + stT188 127 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 126
    simpa using h
  have hprev := st188_p126
  have hstep := st188_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p128 : ((4743350795589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT188 (i+1))
      = (∑ i ∈ Finset.range 127, stT188 (i+1)) + stT188 128 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 127
    simpa using h
  have hprev := st188_p127
  have hstep := st188_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p129 : ((1435390051061/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT188 (i+1))
      = (∑ i ∈ Finset.range 128, stT188 (i+1)) + stT188 129 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 128
    simpa using h
  have hprev := st188_p128
  have hstep := st188_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p130 : ((5833200924961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT188 (i+1))
      = (∑ i ∈ Finset.range 129, stT188 (i+1)) + stT188 130 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 129
    simpa using h
  have hprev := st188_p129
  have hstep := st188_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p131 : ((6041791420607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT188 (i+1))
      = (∑ i ∈ Finset.range 130, stT188 (i+1)) + stT188 131 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 130
    simpa using h
  have hprev := st188_p130
  have hstep := st188_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p132 : ((6007127308293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT188 (i+1))
      = (∑ i ∈ Finset.range 131, stT188 (i+1)) + stT188 132 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 131
    simpa using h
  have hprev := st188_p131
  have hstep := st188_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p133 : ((2895172953149/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT188 (i+1))
      = (∑ i ∈ Finset.range 132, stT188 (i+1)) + stT188 133 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 132
    simpa using h
  have hprev := st188_p132
  have hstep := st188_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p134 : ((23028367668179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT188 (i+1))
      = (∑ i ∈ Finset.range 133, stT188 (i+1)) + stT188 134 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 133
    simpa using h
  have hprev := st188_p133
  have hstep := st188_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p135 : ((4768644703043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT188 (i+1))
      = (∑ i ∈ Finset.range 134, stT188 (i+1)) + stT188 135 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 134
    simpa using h
  have hprev := st188_p134
  have hstep := st188_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p136 : ((24262465931379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT188 (i+1))
      = (∑ i ∈ Finset.range 135, stT188 (i+1)) + stT188 136 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 135
    simpa using h
  have hprev := st188_p135
  have hstep := st188_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p137 : ((23611399000047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT188 (i+1))
      = (∑ i ∈ Finset.range 136, stT188 (i+1)) + stT188 137 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 136
    simpa using h
  have hprev := st188_p136
  have hstep := st188_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p138 : ((11470186342929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT188 (i+1))
      = (∑ i ∈ Finset.range 137, stT188 (i+1)) + stT188 138 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 137
    simpa using h
  have hprev := st188_p137
  have hstep := st188_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p139 : ((466177511923/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT188 (i+1))
      = (∑ i ∈ Finset.range 138, stT188 (i+1)) + stT188 139 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 138
    simpa using h
  have hprev := st188_p138
  have hstep := st188_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p140 : ((12066212039647/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT188 (i+1))
      = (∑ i ∈ Finset.range 139, stT188 (i+1)) + stT188 140 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 139
    simpa using h
  have hprev := st188_p139
  have hstep := st188_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p141 : ((12068864815297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT188 (i+1))
      = (∑ i ∈ Finset.range 140, stT188 (i+1)) + stT188 141 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 140
    simpa using h
  have hprev := st188_p140
  have hstep := st188_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p142 : ((5831071545429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT188 (i+1))
      = (∑ i ∈ Finset.range 141, stT188 (i+1)) + stT188 142 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 141
    simpa using h
  have hprev := st188_p141
  have hstep := st188_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p143 : ((2865415966631/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT188 (i+1))
      = (∑ i ∈ Finset.range 142, stT188 (i+1)) + stT188 143 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 142
    simpa using h
  have hprev := st188_p142
  have hstep := st188_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p144 : ((588172853957/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT188 (i+1))
      = (∑ i ∈ Finset.range 143, stT188 (i+1)) + stT188 144 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 143
    simpa using h
  have hprev := st188_p143
  have hstep := st188_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p145 : ((757469016637/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT188 (i+1))
      = (∑ i ∈ Finset.range 144, stT188 (i+1)) + stT188 145 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 144
    simpa using h
  have hprev := st188_p144
  have hstep := st188_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p146 : ((6006218852789/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT188 (i+1))
      = (∑ i ∈ Finset.range 145, stT188 (i+1)) + stT188 146 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 145
    simpa using h
  have hprev := st188_p145
  have hstep := st188_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p147 : ((2900040331333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT188 (i+1))
      = (∑ i ∈ Finset.range 146, stT188 (i+1)) + stT188 147 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 146
    simpa using h
  have hprev := st188_p146
  have hstep := st188_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p148 : ((22940089719599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT188 (i+1))
      = (∑ i ∈ Finset.range 147, stT188 (i+1)) + stT188 148 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 147
    simpa using h
  have hprev := st188_p147
  have hstep := st188_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p149 : ((23603521006481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT188 (i+1))
      = (∑ i ∈ Finset.range 148, stT188 (i+1)) + stT188 149 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 148
    simpa using h
  have hprev := st188_p148
  have hstep := st188_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p150 : ((4852583655421/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT188 (i+1))
      = (∑ i ∈ Finset.range 149, stT188 (i+1)) + stT188 150 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 149
    simpa using h
  have hprev := st188_p149
  have hstep := st188_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p151 : ((24015368546039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT188 (i+1))
      = (∑ i ∈ Finset.range 150, stT188 (i+1)) + stT188 151 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 150
    simpa using h
  have hprev := st188_p150
  have hstep := st188_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p152 : ((928175840043/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT188 (i+1))
      = (∑ i ∈ Finset.range 151, stT188 (i+1)) + stT188 152 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 151
    simpa using h
  have hprev := st188_p151
  have hstep := st188_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p153 : ((11460221931169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT188 (i+1))
      = (∑ i ∈ Finset.range 152, stT188 (i+1)) + stT188 153 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 152
    simpa using h
  have hprev := st188_p152
  have hstep := st188_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p154 : ((11767099094319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT188 (i+1))
      = (∑ i ∈ Finset.range 153, stT188 (i+1)) + stT188 154 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 153
    simpa using h
  have hprev := st188_p153
  have hstep := st188_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p155 : ((4846878139433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT188 (i+1))
      = (∑ i ∈ Finset.range 154, stT188 (i+1)) + stT188 155 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 154
    simpa using h
  have hprev := st188_p154
  have hstep := st188_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p156 : ((24114561961259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT188 (i+1))
      = (∑ i ∈ Finset.range 155, stT188 (i+1)) + stT188 156 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 155
    simpa using h
  have hprev := st188_p155
  have hstep := st188_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p157 : ((729236088349/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT188 (i+1))
      = (∑ i ∈ Finset.range 156, stT188 (i+1)) + stT188 157 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 156
    simpa using h
  have hprev := st188_p156
  have hstep := st188_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p158 : ((11444311138069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT188 (i+1))
      = (∑ i ∈ Finset.range 157, stT188 (i+1)) + stT188 158 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 157
    simpa using h
  have hprev := st188_p157
  have hstep := st188_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p159 : ((23329573700107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT188 (i+1))
      = (∑ i ∈ Finset.range 158, stT188 (i+1)) + stT188 159 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 158
    simpa using h
  have hprev := st188_p158
  have hstep := st188_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p160 : ((12052364488157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT188 (i+1))
      = (∑ i ∈ Finset.range 159, stT188 (i+1)) + stT188 160 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 159
    simpa using h
  have hprev := st188_p159
  have hstep := st188_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p161 : ((12131374879987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT188 (i+1))
      = (∑ i ∈ Finset.range 160, stT188 (i+1)) + stT188 161 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 160
    simpa using h
  have hprev := st188_p160
  have hstep := st188_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p162 : ((23618115207599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT188 (i+1))
      = (∑ i ∈ Finset.range 161, stT188 (i+1)) + stT188 162 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 161
    simpa using h
  have hprev := st188_p161
  have hstep := st188_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p163 : ((22949634841061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT188 (i+1))
      = (∑ i ∈ Finset.range 162, stT188 (i+1)) + stT188 163 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 162
    simpa using h
  have hprev := st188_p162
  have hstep := st188_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p164 : ((4609755236989/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT188 (i+1))
      = (∑ i ∈ Finset.range 163, stT188 (i+1)) + stT188 164 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 163
    simpa using h
  have hprev := st188_p163
  have hstep := st188_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p165 : ((23792329745219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT188 (i+1))
      = (∑ i ∈ Finset.range 164, stT188 (i+1)) + stT188 165 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 164
    simpa using h
  have hprev := st188_p164
  have hstep := st188_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p166 : ((24313015405769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT188 (i+1))
      = (∑ i ∈ Finset.range 165, stT188 (i+1)) + stT188 166 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 165
    simpa using h
  have hprev := st188_p165
  have hstep := st188_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p167 : ((24016120804041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT188 (i+1))
      = (∑ i ∈ Finset.range 166, stT188 (i+1)) + stT188 167 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 166
    simpa using h
  have hprev := st188_p166
  have hstep := st188_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p168 : ((23245719417623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT188 (i+1))
      = (∑ i ∈ Finset.range 167, stT188 (i+1)) + stT188 168 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 167
    simpa using h
  have hprev := st188_p167
  have hstep := st188_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p169 : ((22870323920389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT188 (i+1))
      = (∑ i ∈ Finset.range 168, stT188 (i+1)) + stT188 169 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 168
    simpa using h
  have hprev := st188_p168
  have hstep := st188_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p170 : ((23302958342257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT188 (i+1))
      = (∑ i ∈ Finset.range 169, stT188 (i+1)) + stT188 170 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 169
    simpa using h
  have hprev := st188_p169
  have hstep := st188_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p171 : ((4812212810469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT188 (i+1))
      = (∑ i ∈ Finset.range 170, stT188 (i+1)) + stT188 171 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 170
    simpa using h
  have hprev := st188_p170
  have hstep := st188_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p172 : ((4863543771909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT188 (i+1))
      = (∑ i ∈ Finset.range 171, stT188 (i+1)) + stT188 172 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 171
    simpa using h
  have hprev := st188_p171
  have hstep := st188_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p173 : ((23801391910653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT188 (i+1))
      = (∑ i ∈ Finset.range 172, stT188 (i+1)) + stT188 173 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 172
    simpa using h
  have hprev := st188_p172
  have hstep := st188_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p174 : ((23068593706679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT188 (i+1))
      = (∑ i ∈ Finset.range 173, stT188 (i+1)) + stT188 174 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 173
    simpa using h
  have hprev := st188_p173
  have hstep := st188_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p175 : ((22893169799223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT188 (i+1))
      = (∑ i ∈ Finset.range 174, stT188 (i+1)) + stT188 175 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 174
    simpa using h
  have hprev := st188_p174
  have hstep := st188_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p176 : ((23452953985587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT188 (i+1))
      = (∑ i ∈ Finset.range 175, stT188 (i+1)) + stT188 176 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 175
    simpa using h
  have hprev := st188_p175
  have hstep := st188_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p177 : ((24163651063153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT188 (i+1))
      = (∑ i ∈ Finset.range 176, stT188 (i+1)) + stT188 177 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 176
    simpa using h
  have hprev := st188_p176
  have hstep := st188_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p178 : ((24297943033361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT188 (i+1))
      = (∑ i ∈ Finset.range 177, stT188 (i+1)) + stT188 178 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 177
    simpa using h
  have hprev := st188_p177
  have hstep := st188_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p179 : ((4745031183773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT188 (i+1))
      = (∑ i ∈ Finset.range 178, stT188 (i+1)) + stT188 179 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 178
    simpa using h
  have hprev := st188_p178
  have hstep := st188_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p180 : ((23024847744793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT188 (i+1))
      = (∑ i ∈ Finset.range 179, stT188 (i+1)) + stT188 180 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 179
    simpa using h
  have hprev := st188_p179
  have hstep := st188_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p181 : ((5722999471537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT188 (i+1))
      = (∑ i ∈ Finset.range 180, stT188 (i+1)) + stT188 181 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 180
    simpa using h
  have hprev := st188_p180
  have hstep := st188_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p182 : ((23451849172117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT188 (i+1))
      = (∑ i ∈ Finset.range 181, stT188 (i+1)) + stT188 182 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 181
    simpa using h
  have hprev := st188_p181
  have hstep := st188_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p183 : ((12077272261643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT188 (i+1))
      = (∑ i ∈ Finset.range 182, stT188 (i+1)) + stT188 183 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 182
    simpa using h
  have hprev := st188_p182
  have hstep := st188_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p184 : ((6080780526329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT188 (i+1))
      = (∑ i ∈ Finset.range 183, stT188 (i+1)) + stT188 184 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 183
    simpa using h
  have hprev := st188_p183
  have hstep := st188_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p185 : ((11900873664463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT188 (i+1))
      = (∑ i ∈ Finset.range 184, stT188 (i+1)) + stT188 185 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 184
    simpa using h
  have hprev := st188_p184
  have hstep := st188_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p186 : ((11543966275429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT188 (i+1))
      = (∑ i ∈ Finset.range 185, stT188 (i+1)) + stT188 186 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 185
    simpa using h
  have hprev := st188_p185
  have hstep := st188_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p187 : ((22849652362719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT188 (i+1))
      = (∑ i ∈ Finset.range 186, stT188 (i+1)) + stT188 187 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 186
    simpa using h
  have hprev := st188_p186
  have hstep := st188_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p188 : ((23302978281399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT188 (i+1))
      = (∑ i ∈ Finset.range 187, stT188 (i+1)) + stT188 188 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 187
    simpa using h
  have hprev := st188_p187
  have hstep := st188_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p189 : ((4805377651179/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT188 (i+1))
      = (∑ i ∈ Finset.range 188, stT188 (i+1)) + stT188 189 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 188
    simpa using h
  have hprev := st188_p188
  have hstep := st188_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p190 : ((4872545846639/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT188 (i+1))
      = (∑ i ∈ Finset.range 189, stT188 (i+1)) + stT188 190 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 189
    simpa using h
  have hprev := st188_p189
  have hstep := st188_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p191 : ((1200614043851/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT188 (i+1))
      = (∑ i ∈ Finset.range 190, stT188 (i+1)) + stT188 191 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 190
    simpa using h
  have hprev := st188_p190
  have hstep := st188_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p192 : ((5823268329669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT188 (i+1))
      = (∑ i ∈ Finset.range 191, stT188 (i+1)) + stT188 192 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 191
    simpa using h
  have hprev := st188_p191
  have hstep := st188_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p193 : ((5710425654613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT188 (i+1))
      = (∑ i ∈ Finset.range 192, stT188 (i+1)) + stT188 193 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 192
    simpa using h
  have hprev := st188_p192
  have hstep := st188_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p194 : ((5762407249729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT188 (i+1))
      = (∑ i ∈ Finset.range 193, stT188 (i+1)) + stT188 194 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 193
    simpa using h
  have hprev := st188_p193
  have hstep := st188_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p195 : ((11865748855661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT188 (i+1))
      = (∑ i ∈ Finset.range 194, stT188 (i+1)) + stT188 195 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 194
    simpa using h
  have hprev := st188_p194
  have hstep := st188_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p196 : ((24299532143287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT188 (i+1))
      = (∑ i ∈ Finset.range 195, stT188 (i+1)) + stT188 196 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 195
    simpa using h
  have hprev := st188_p195
  have hstep := st188_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p197 : ((12136481693613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT188 (i+1))
      = (∑ i ∈ Finset.range 196, stT188 (i+1)) + stT188 197 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 196
    simpa using h
  have hprev := st188_p196
  have hstep := st188_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p198 : ((11839560214263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT188 (i+1))
      = (∑ i ∈ Finset.range 197, stT188 (i+1)) + stT188 198 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 197
    simpa using h
  have hprev := st188_p197
  have hstep := st188_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p199 : ((5754254565147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT188 (i+1))
      = (∑ i ∈ Finset.range 198, stT188 (i+1)) + stT188 199 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 198
    simpa using h
  have hprev := st188_p198
  have hstep := st188_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p200 : ((22833159833983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT188 (i+1))
      = (∑ i ∈ Finset.range 199, stT188 (i+1)) + stT188 200 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 199
    simpa using h
  have hprev := st188_p199
  have hstep := st188_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p201 : ((23273718320983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT188 (i+1))
      = (∑ i ∈ Finset.range 200, stT188 (i+1)) + stT188 201 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 200
    simpa using h
  have hprev := st188_p200
  have hstep := st188_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p202 : ((23976801695173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT188 (i+1))
      = (∑ i ∈ Finset.range 201, stT188 (i+1)) + stT188 202 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 201
    simpa using h
  have hprev := st188_p201
  have hstep := st188_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p203 : ((4875252027143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT188 (i+1))
      = (∑ i ∈ Finset.range 202, stT188 (i+1)) + stT188 203 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 202
    simpa using h
  have hprev := st188_p202
  have hstep := st188_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p204 : ((24157107601023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT188 (i+1))
      = (∑ i ∈ Finset.range 203, stT188 (i+1)) + stT188 204 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 203
    simpa using h
  have hprev := st188_p203
  have hstep := st188_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p205 : ((23497047003301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT188 (i+1))
      = (∑ i ∈ Finset.range 204, stT188 (i+1)) + stT188 205 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 204
    simpa using h
  have hprev := st188_p204
  have hstep := st188_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p206 : ((22914862343507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT188 (i+1))
      = (∑ i ∈ Finset.range 205, stT188 (i+1)) + stT188 206 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 205
    simpa using h
  have hprev := st188_p205
  have hstep := st188_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p207 : ((22860178668383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT188 (i+1))
      = (∑ i ∈ Finset.range 206, stT188 (i+1)) + stT188 207 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 206
    simpa using h
  have hprev := st188_p206
  have hstep := st188_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p208 : ((2921318987251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT188 (i+1))
      = (∑ i ∈ Finset.range 207, stT188 (i+1)) + stT188 208 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 207
    simpa using h
  have hprev := st188_p207
  have hstep := st188_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p209 : ((12026796248081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT188 (i+1))
      = (∑ i ∈ Finset.range 208, stT188 (i+1)) + stT188 209 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 208
    simpa using h
  have hprev := st188_p208
  have hstep := st188_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p210 : ((12196781339661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT188 (i+1))
      = (∑ i ∈ Finset.range 209, stT188 (i+1)) + stT188 210 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 209
    simpa using h
  have hprev := st188_p209
  have hstep := st188_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p211 : ((377179913737/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT188 (i+1))
      = (∑ i ∈ Finset.range 210, stT188 (i+1)) + stT188 211 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 210
    simpa using h
  have hprev := st188_p210
  have hstep := st188_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p212 : ((23484170490583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT188 (i+1))
      = (∑ i ∈ Finset.range 211, stT188 (i+1)) + stT188 212 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 211
    simpa using h
  have hprev := st188_p211
  have hstep := st188_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p213 : ((22911264782391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT188 (i+1))
      = (∑ i ∈ Finset.range 212, stT188 (i+1)) + stT188 213 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 212
    simpa using h
  have hprev := st188_p212
  have hstep := st188_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p214 : ((22836513286119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT188 (i+1))
      = (∑ i ∈ Finset.range 213, stT188 (i+1)) + stT188 214 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 213
    simpa using h
  have hprev := st188_p213
  have hstep := st188_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p215 : ((23309736646827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT188 (i+1))
      = (∑ i ∈ Finset.range 214, stT188 (i+1)) + stT188 215 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 214
    simpa using h
  have hprev := st188_p214
  have hstep := st188_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p216 : ((23988518016453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT188 (i+1))
      = (∑ i ∈ Finset.range 215, stT188 (i+1)) + stT188 216 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 215
    simpa using h
  have hprev := st188_p215
  have hstep := st188_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p217 : ((24390562696609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT188 (i+1))
      = (∑ i ∈ Finset.range 216, stT188 (i+1)) + stT188 217 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 216
    simpa using h
  have hprev := st188_p216
  have hstep := st188_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p218 : ((4847164091009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT188 (i+1))
      = (∑ i ∈ Finset.range 217, stT188 (i+1)) + stT188 218 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 217
    simpa using h
  have hprev := st188_p217
  have hstep := st188_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p219 : ((23636384762791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT188 (i+1))
      = (∑ i ∈ Finset.range 218, stT188 (i+1)) + stT188 219 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 218
    simpa using h
  have hprev := st188_p218
  have hstep := st188_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p220 : ((23009391572591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT188 (i+1))
      = (∑ i ∈ Finset.range 219, stT188 (i+1)) + stT188 220 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 219
    simpa using h
  have hprev := st188_p219
  have hstep := st188_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p221 : ((5696002952817/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT188 (i+1))
      = (∑ i ∈ Finset.range 220, stT188 (i+1)) + stT188 221 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 220
    simpa using h
  have hprev := st188_p220
  have hstep := st188_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p222 : ((5777485989309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT188 (i+1))
      = (∑ i ∈ Finset.range 221, stT188 (i+1)) + stT188 222 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 221
    simpa using h
  have hprev := st188_p221
  have hstep := st188_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p223 : ((5940901774077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT188 (i+1))
      = (∑ i ∈ Finset.range 222, stT188 (i+1)) + stT188 223 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 222
    simpa using h
  have hprev := st188_p222
  have hstep := st188_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p224 : ((12153206628601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT188 (i+1))
      = (∑ i ∈ Finset.range 223, stT188 (i+1)) + stT188 224 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 223
    simpa using h
  have hprev := st188_p223
  have hstep := st188_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p225 : ((12190084591723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT188 (i+1))
      = (∑ i ∈ Finset.range 224, stT188 (i+1)) + stT188 225 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 224
    simpa using h
  have hprev := st188_p224
  have hstep := st188_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p226 : ((23940128707171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT188 (i+1))
      = (∑ i ∈ Finset.range 225, stT188 (i+1)) + stT188 226 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 225
    simpa using h
  have hprev := st188_p225
  have hstep := st188_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p227 : ((23276479044259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT188 (i+1))
      = (∑ i ∈ Finset.range 226, stT188 (i+1)) + stT188 227 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 226
    simpa using h
  have hprev := st188_p226
  have hstep := st188_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p228 : ((22819041955621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT188 (i+1))
      = (∑ i ∈ Finset.range 227, stT188 (i+1)) + stT188 228 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 227
    simpa using h
  have hprev := st188_p227
  have hstep := st188_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p229 : ((22858869456481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT188 (i+1))
      = (∑ i ∈ Finset.range 228, stT188 (i+1)) + stT188 229 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 228
    simpa using h
  have hprev := st188_p228
  have hstep := st188_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p230 : ((23366848555301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT188 (i+1))
      = (∑ i ∈ Finset.range 229, stT188 (i+1)) + stT188 230 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 229
    simpa using h
  have hprev := st188_p229
  have hstep := st188_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p231 : ((24019685960129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT188 (i+1))
      = (∑ i ∈ Finset.range 230, stT188 (i+1)) + stT188 231 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 230
    simpa using h
  have hprev := st188_p230
  have hstep := st188_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p232 : ((24408754701713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT188 (i+1))
      = (∑ i ∈ Finset.range 231, stT188 (i+1)) + stT188 232 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 231
    simpa using h
  have hprev := st188_p231
  have hstep := st188_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p233 : ((24295145409839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT188 (i+1))
      = (∑ i ∈ Finset.range 232, stT188 (i+1)) + stT188 233 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 232
    simpa using h
  have hprev := st188_p232
  have hstep := st188_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p234 : ((23752419698429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT188 (i+1))
      = (∑ i ∈ Finset.range 233, stT188 (i+1)) + stT188 234 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 233
    simpa using h
  have hprev := st188_p233
  have hstep := st188_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p235 : ((5778607711709/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT188 (i+1))
      = (∑ i ∈ Finset.range 234, stT188 (i+1)) + stT188 235 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 234
    simpa using h
  have hprev := st188_p234
  have hstep := st188_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p236 : ((22767420529621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT188 (i+1))
      = (∑ i ∈ Finset.range 235, stT188 (i+1)) + stT188 236 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 235
    simpa using h
  have hprev := st188_p235
  have hstep := st188_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p237 : ((11458601997881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT188 (i+1))
      = (∑ i ∈ Finset.range 236, stT188 (i+1)) + stT188 237 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 236
    simpa using h
  have hprev := st188_p236
  have hstep := st188_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p238 : ((23470967059677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT188 (i+1))
      = (∑ i ∈ Finset.range 237, stT188 (i+1)) + stT188 238 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 237
    simpa using h
  have hprev := st188_p237
  have hstep := st188_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p239 : ((24098966554621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT188 (i+1))
      = (∑ i ∈ Finset.range 238, stT188 (i+1)) + stT188 239 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 238
    simpa using h
  have hprev := st188_p238
  have hstep := st188_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p240 : ((24433043526971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT188 (i+1))
      = (∑ i ∈ Finset.range 239, stT188 (i+1)) + stT188 240 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 239
    simpa using h
  have hprev := st188_p239
  have hstep := st188_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p241 : ((94849055003/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT188 (i+1))
      = (∑ i ∈ Finset.range 240, stT188 (i+1)) + stT188 241 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 240
    simpa using h
  have hprev := st188_p240
  have hstep := st188_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p242 : ((11867437917409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT188 (i+1))
      = (∑ i ∈ Finset.range 241, stT188 (i+1)) + stT188 242 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 241
    simpa using h
  have hprev := st188_p241
  have hstep := st188_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p243 : ((23108886970499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT188 (i+1))
      = (∑ i ∈ Finset.range 242, stT188 (i+1)) + stT188 243 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 242
    simpa using h
  have hprev := st188_p242
  have hstep := st188_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p244 : ((22759020746519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT188 (i+1))
      = (∑ i ∈ Finset.range 243, stT188 (i+1)) + stT188 244 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 243
    simpa using h
  have hprev := st188_p243
  have hstep := st188_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p245 : ((22880136941971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT188 (i+1))
      = (∑ i ∈ Finset.range 244, stT188 (i+1)) + stT188 245 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 244
    simpa using h
  have hprev := st188_p244
  have hstep := st188_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p246 : ((23401145559467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT188 (i+1))
      = (∑ i ∈ Finset.range 245, stT188 (i+1)) + stT188 246 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 245
    simpa using h
  have hprev := st188_p245
  have hstep := st188_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p247 : ((24030399257551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT188 (i+1))
      = (∑ i ∈ Finset.range 246, stT188 (i+1)) + stT188 247 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 246
    simpa using h
  have hprev := st188_p246
  have hstep := st188_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p248 : ((24421073482551/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT188 (i+1))
      = (∑ i ∈ Finset.range 247, stT188 (i+1)) + stT188 248 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 247
    simpa using h
  have hprev := st188_p247
  have hstep := st188_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p249 : ((24361695984951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT188 (i+1))
      = (∑ i ∈ Finset.range 248, stT188 (i+1)) + stT188 249 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 248
    simpa using h
  have hprev := st188_p248
  have hstep := st188_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_p250 : ((23887638590151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT188 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT188 (i+1))
      = (∑ i ∈ Finset.range 249, stT188 (i+1)) + stT188 250 := by
    have h := Finset.sum_range_succ (fun i => stT188 (i+1)) 249
    simpa using h
  have hprev := st188_p249
  have hstep := st188_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st188_s250 :
    |Real.sin (((188 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))
      - ((165501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 6045257/10000000) (δ := 9517/1000000000) (ψ := -55451/50000) 188 165
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 188`** (evaluated boundary). -/
theorem station_188_sign : 0 < hardyG ((((188:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 188 250 (by norm_num) (by norm_num)
    ((-55451/50000 : ℚ) : ℝ)
  have hchain := st188_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT188 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((188 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-55451/50000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st188_c250
  have hsinb := abs_le.mp st188_s250
  have hbdy_lo : ((-9810295944339/176721250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((188 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-55451/50000 : ℚ) : ℝ))) / 2
          - ((((188:ℕ)):ℝ))
            * Real.sin (((188 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-55451/50000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((188:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((188:ℝ) * Real.log (250:ℝ) - ((-55451/50000 : ℚ) : ℝ))) / 2
        - ((188:ℝ)) * Real.sin ((188:ℝ) * Real.log (250:ℝ) - ((-55451/50000 : ℚ) : ℝ))
        ≥ ((-124091427/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((188:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-124091427/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-124091427/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-124091427/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((188:ℕ)):ℝ))+1) * (((((188:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((49575933187/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((23887638590151/10000000000000 : ℚ) : ℝ) + ((-9810295944339/176721250000000 : ℚ) : ℝ)
      - ((49575933187/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-55451/50000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((188:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-55451/50000 : ℚ) : ℝ)
        * (riemannZeta (line ((((188:ℕ)):ℝ)))).re
      - Real.sin ((-55451/50000 : ℚ) : ℝ)
        * (riemannZeta (line ((((188:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((188:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((188:ℕ)):ℝ))
      = (((((188:ℕ)):ℝ)) * (Real.log ((((188:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((188:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_188
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
  have hθwin : |(((-55451/50000 : ℚ) : ℝ) + ((36:ℤ)) * (2*Real.pi)) - theta ((((188:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((188:ℕ)):ℝ)))
    (φ := ((-55451/50000 : ℚ) : ℝ) + ((36:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-55451/50000 : ℚ)) : ℝ) 36).1,
    (cos_sin_shift (((-55451/50000 : ℚ)) : ℝ) 36).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_188_sign
end AxiomAudit
