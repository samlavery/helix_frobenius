import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 166` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT166 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((166 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))

theorem st166_c1 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((124043/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77387/2500000) (δ := 201/1000000000) (ψ := -123819/1000000) 166 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t1 : ((496147/500000 : ℚ) : ℝ) ≤ stT166 1 := by
  have hc : ((496147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496147/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((496147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c2 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-495243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1305569/2500000) (δ := 8331/1000000000) (ψ := -123819/1000000) 166 18
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t2 : ((-875562620731/2500000000000 : ℚ) : ℝ) ≤ stT166 2 := by
  have hc : ((-495293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-875562620731/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-495293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c3 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((960757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 87837/1250000) (δ := 8493/1000000000) (ψ := -123819/1000000) 166 29
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t3 : ((2773321892957/5000000000000 : ℚ) : ℝ) ≤ stT166 3 := by
  have hc : ((960707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2773321892957/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((960707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c4 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-122367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2786469/5000000) (δ := 8367/1000000000) (ψ := -123819/1000000) 166 37
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t4 : ((-611885122377/2000000000000 : ℚ) : ℝ) ≤ stT166 4 := by
  have hc : ((-122377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-611885122377/2000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-122377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c5 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-967627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1804031/2500000) (δ := 8393/1000000000) (ψ := -123819/1000000) 166 43
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t5 : ((-540947893509/1250000000000 : ℚ) : ℝ) ≤ stT166 5 := by
  have hc : ((-967677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-540947893509/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-967677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c6 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-156299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2807723/5000000) (δ := 8439/1000000000) (ψ := -123819/1000000) 166 47
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t6 : ((-1276278082909/5000000000000 : ℚ) : ℝ) ≤ stT166 6 := by
  have hc : ((-312623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1276278082909/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-312623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c7 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-452559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6756133/10000000) (δ := 1667/200000000) (ψ := -123819/1000000) 166 51
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t7 : ((-42765171317/125000000000 : ℚ) : ℝ) ≤ stT166 7 := by
  have hc : ((-56573/62500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42765171317/125000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-56573/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c8 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((482667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660189/10000000) (δ := 8307/1000000000) (ψ := -123819/1000000) 166 55
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t8 : ((853198359093/2500000000000 : ℚ) : ℝ) ≤ stT166 8 := by
  have hc : ((241321/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((853198359093/2500000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((241321/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c9 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((181091/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547933/5000000) (δ := 1677/200000000) (ψ := -123819/1000000) 166 58
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t9 : ((603603272973/2000000000000 : ℚ) : ℝ) ≤ stT166 9 := by
  have hc : ((181081/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((603603272973/2000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((181081/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c10 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((151183/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287927/1250000) (δ := 8339/1000000000) (ψ := -123819/1000000) 166 61
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t10 : ((956085990457/5000000000000 : ℚ) : ℝ) ≤ stT166 10 := by
  have hc : ((302341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956085990457/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((302341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c11 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-86383/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 583439/1000000) (δ := 8449/1000000000) (ψ := -123819/1000000) 166 63
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t11 : ((-520946874249/2500000000000 : ℚ) : ℝ) ≤ stT166 11 := by
  have hc : ((-345557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-520946874249/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-345557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c12 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-1201/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647471/1250000) (δ := 339/40000000) (ψ := -123819/1000000) 166 66
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t12 : ((-866837499/6250000000 : ℚ) : ℝ) ≤ stT166 12 := by
  have hc : ((-9609/20000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866837499/6250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-9609/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c13 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((108923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1688987/5000000) (δ := 849/100000000) (ψ := -123819/1000000) 166 68
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t13 : ((302028603/5000000000 : ℚ) : ℝ) ≤ stT166 13 := by
  have hc : ((54449/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((302028603/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((54449/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c14 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-44821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4039081/10000000) (δ := 519/62500000) (ψ := -123819/1000000) 166 70
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t14 : ((-119922817923/10000000000000 : ℚ) : ℝ) ≤ stT166 14 := by
  have hc : ((-44871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119922817923/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-44871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c15 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-916157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3411477/5000000) (δ := 4159/500000000) (ψ := -123819/1000000) 166 72
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t15 : ((-2365636395723/10000000000000 : ℚ) : ℝ) ≤ stT166 15 := by
  have hc : ((-916207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2365636395723/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-916207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c16 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-6493/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53157/125000) (δ := 8377/1000000000) (ψ := -123819/1000000) 166 73
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t16 : ((-32477512991/1000000000000 : ℚ) : ℝ) ≤ stT166 16 := by
  have hc : ((-12991/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32477512991/1000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-12991/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c17 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((695513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2004157/10000000) (δ := 211/25000000) (ψ := -123819/1000000) 166 75
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t17 : ((421686339957/2500000000000 : ℚ) : ℝ) ≤ stT166 17 := by
  have hc : ((695463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((421686339957/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((695463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c18 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-739717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1201723/2000000) (δ := 1057/125000000) (ψ := -123819/1000000) 166 76
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t18 : ((-1743647833641/10000000000000 : ℚ) : ℝ) ≤ stT166 18 := by
  have hc : ((-739767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1743647833641/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-739767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c19 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((37373/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2969423/10000000) (δ := 4181/500000000) (ψ := -123819/1000000) 166 78
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t19 : ((10716007347/125000000000 : ℚ) : ℝ) ≤ stT166 19 := by
  have hc : ((4671/12500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10716007347/125000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((4671/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c20 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((502997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2609333/10000000) (δ := 4167/500000000) (ψ := -123819/1000000) 166 79
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t20 : ((1124623189449/10000000000000 : ℚ) : ℝ) ≤ stT166 20 := by
  have hc : ((502947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1124623189449/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((502947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c21 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-960537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7149303/10000000) (δ := 1047/125000000) (ψ := -123819/1000000) 166 80
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t21 : ((-2096172779073/10000000000000 : ℚ) : ℝ) ≤ stT166 21 := by
  have hc : ((-960587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2096172779073/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-960587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c22 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-401847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -620103/1250000) (δ := 8413/1000000000) (ψ := -123819/1000000) 166 82
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t22 : ((-107105952397/1250000000000 : ℚ) : ℝ) ≤ stT166 22 := by
  have hc : ((-401897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107105952397/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-401897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c23 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((126113/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222129/1000000) (δ := 4153/500000000) (ψ := -123819/1000000) 166 83
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t23 : ((32867864229/250000000000 : ℚ) : ℝ) ≤ stT166 23 := by
  have hc : ((126103/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32867864229/250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((126103/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c24 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((994301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267019/10000000) (δ := 1681/200000000) (ψ := -123819/1000000) 166 84
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t24 : ((2029505905491/10000000000000 : ℚ) : ℝ) ≤ stT166 24 := by
  have hc : ((994251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2029505905491/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((994251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c25 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((741/800 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 966147/10000000) (δ := 8491/1000000000) (ψ := -123819/1000000) 166 85
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t25 : ((4631/25000 : ℚ) : ℝ) ≤ stT166 25 := by
  have hc : ((4631/5000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4631/25000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((4631/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c26 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((408701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61391/400000) (δ := 8419/1000000000) (ψ := -123819/1000000) 166 86
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t26 : ((200369858209/1250000000000 : ℚ) : ℝ) ≤ stT166 26 := by
  have hc : ((102169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200369858209/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((102169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c27 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((206951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372259/2500000) (δ := 4163/500000000) (ψ := -123819/1000000) 166 87
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t27 : ((1593012573/10000000000 : ℚ) : ℝ) ≤ stT166 27 := by
  have hc : ((413877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1593012573/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((413877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c28 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((187911/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218417/2500000) (δ := 837/100000000) (ψ := -123819/1000000) 166 88
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t28 : ((177549721811/1000000000000 : ℚ) : ℝ) ≤ stT166 28 := by
  have hc : ((187901/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177549721811/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((187901/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c29 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((994113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135703/5000000) (δ := 8463/1000000000) (ψ := -123819/1000000) 166 89
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t29 : ((1845928270039/10000000000000 : ℚ) : ℝ) ≤ stT166 29 := by
  have hc : ((994063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1845928270039/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((994063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c30 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((361003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -955123/5000000) (δ := 33/3906250) (ψ := -123819/1000000) 166 90
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t30 : ((329526167349/2500000000000 : ℚ) : ℝ) ≤ stT166 30 := by
  have hc : ((180489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329526167349/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((180489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c31 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-16679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4010401/10000000) (δ := 1671/200000000) (ψ := -123819/1000000) 166 91
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t31 : ((-234385047/39062500000 : ℚ) : ℝ) ≤ stT166 31 := by
  have hc : ((-522/15625 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234385047/39062500000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-522/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c32 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-865559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3271327/5000000) (δ := 8341/1000000000) (ψ := -123819/1000000) 166 92
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t32 : ((-1530195025103/10000000000000 : ℚ) : ℝ) ≤ stT166 32 := by
  have hc : ((-865609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1530195025103/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-865609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c33 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-39787/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 155689/250000) (δ := 8341/1000000000) (ψ := -123819/1000000) 166 92
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t33 : ((-138529292883/1000000000000 : ℚ) : ℝ) ≤ stT166 33 := by
  have hc : ((-79579/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138529292883/1000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-79579/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c34 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((198093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181787/625000) (δ := 8369/1000000000) (ψ := -123819/1000000) 166 93
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t34 : ((16984182449/250000000000 : ℚ) : ℝ) ≤ stT166 34 := by
  have hc : ((49517/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16984182449/250000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((49517/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c35 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((190599/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769559/10000000) (δ := 8327/1000000000) (ψ := -123819/1000000) 166 94
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t35 : ((80538527853/500000000000 : ℚ) : ℝ) ≤ stT166 35 := by
  have hc : ((190589/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80538527853/500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((190589/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c36 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-84277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4786599/10000000) (δ := 8419/1000000000) (ψ := -123819/1000000) 166 95
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t36 : ((-280965056193/5000000000000 : ℚ) : ℝ) ≤ stT166 36 := by
  have hc : ((-168579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280965056193/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-168579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c37 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-21843/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3291993/5000000) (δ := 8419/1000000000) (ψ := -123819/1000000) 166 95
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t37 : ((-14364691423/100000000000 : ℚ) : ℝ) ≤ stT166 37 := by
  have hc : ((-87377/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14364691423/100000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-87377/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c38 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((178197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 971663/5000000) (δ := 1039/125000000) (ψ := -123819/1000000) 166 96
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t38 : ((289053390483/2500000000000 : ℚ) : ℝ) ≤ stT166 38 := by
  have hc : ((356369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289053390483/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((356369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c39 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((23001/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -596961/2000000) (δ := 1681/200000000) (ψ := -123819/1000000) 166 97
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t39 : ((294608482223/5000000000000 : ℚ) : ℝ) ≤ stT166 39 := by
  have hc : ((183983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294608482223/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((183983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c40 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-1239/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3761041/5000000) (δ := 1681/200000000) (ψ := -123819/1000000) 166 97
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t40 : ((-1253843227/8000000000 : ℚ) : ℝ) ≤ stT166 40 := by
  have hc : ((-793/800 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1253843227/8000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-793/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c41 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((678837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 515387/2500000) (δ := 1661/200000000) (ψ := -123819/1000000) 166 98
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t41 : ((1060086773019/10000000000000 : ℚ) : ℝ) ≤ stT166 41 := by
  have hc : ((678787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1060086773019/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((678787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c42 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((22439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3645911/10000000) (δ := 2103/250000000) (ψ := -123819/1000000) 166 99
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t42 : ((34608687157/2000000000000 : ℚ) : ℝ) ≤ stT166 42 := by
  have hc : ((22429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34608687157/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((22429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c43 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-768761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3059623/5000000) (δ := 8391/1000000000) (ψ := -123819/1000000) 166 99
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t43 : ((-586213005823/5000000000000 : ℚ) : ℝ) ≤ stT166 43 := by
  have hc : ((-768811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-586213005823/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-768811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c44 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((199963/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923/400000) (δ := 2121/250000000) (ψ := -123819/1000000) 166 100
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t44 : ((75360086217/500000000000 : ℚ) : ℝ) ≤ stT166 44 := by
  have hc : ((199953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75360086217/500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((199953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c45 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-842083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3214913/5000000) (δ := 1047/125000000) (ψ := -123819/1000000) 166 101
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t45 : ((-156922221087/1250000000000 : ℚ) : ℝ) ≤ stT166 45 := by
  have hc : ((-842133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156922221087/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-842133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c46 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((474353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345709/5000000) (δ := 8427/1000000000) (ψ := -123819/1000000) 166 101
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t46 : ((699321354957/10000000000000 : ℚ) : ℝ) ≤ stT166 46 := by
  have hc : ((474303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((699321354957/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((474303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c47 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-65729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4091431/10000000) (δ := 4167/500000000) (ψ := -123819/1000000) 166 102
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t47 : ((-1918970767/200000000000 : ℚ) : ℝ) ≤ stT166 47 := by
  have hc : ((-65779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1918970767/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-65779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c48 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-8861/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464573/1000000) (δ := 4167/500000000) (ψ := -123819/1000000) 166 102
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t48 : ((-12792010011/312500000000 : ℚ) : ℝ) ≤ stT166 48 := by
  have hc : ((-141801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12792010011/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-141801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c49 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((538529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501053/2000000) (δ := 8441/1000000000) (ψ := -123819/1000000) 166 103
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t49 : ((769255483509/10000000000000 : ℚ) : ℝ) ≤ stT166 49 := by
  have hc : ((538479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((769255483509/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((538479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c50 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-703821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5878897/10000000) (δ := 8441/1000000000) (ψ := -123819/1000000) 166 103
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t50 : ((-497712111197/5000000000000 : ℚ) : ℝ) ≤ stT166 50 := by
  have hc : ((-703871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497712111197/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-703871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c51 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((799463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -402747/2500000) (δ := 1691/200000000) (ψ := -123819/1000000) 166 104
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t51 : ((27985050891/250000000000 : ℚ) : ℝ) ≤ stT166 51 := by
  have hc : ((799413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27985050891/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((799413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c52 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-21147/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1611881/2500000) (δ := 2087/250000000) (ψ := -123819/1000000) 166 104
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t52 : ((-117309427343/1000000000000 : ℚ) : ℝ) ≤ stT166 52 := by
  have hc : ((-84593/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117309427343/1000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-84593/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c53 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((856589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338859/2500000) (δ := 1691/200000000) (ψ := -123819/1000000) 166 105
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t53 : ((235309250619/2000000000000 : ℚ) : ℝ) ≤ stT166 53 := by
  have hc : ((856539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((235309250619/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((856539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c54 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-835981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1280357/2000000) (δ := 2087/250000000) (ψ := -123819/1000000) 166 105
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t54 : ((-284423598417/2500000000000 : ℚ) : ℝ) ≤ stT166 54 := by
  have hc : ((-836031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284423598417/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-836031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c55 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((194939/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -845651/5000000) (δ := 211/25000000) (ψ := -123819/1000000) 166 106
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t55 : ((525677395347/5000000000000 : ℚ) : ℝ) ≤ stT166 55 := by
  have hc : ((389853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525677395347/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((389853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c56 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-135411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 723297/1250000) (δ := 8363/1000000000) (ψ := -123819/1000000) 166 106
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t56 : ((-180964030247/2000000000000 : ℚ) : ℝ) ≤ stT166 56 := by
  have hc : ((-135421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180964030247/2000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-135421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c57 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((514389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2576253/10000000) (δ := 847/100000000) (ψ := -123819/1000000) 166 107
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t57 : ((170314616087/2500000000000 : ℚ) : ℝ) ≤ stT166 57 := by
  have hc : ((514339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170314616087/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((514339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c58 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-281869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72521/156250) (δ := 847/100000000) (ψ := -123819/1000000) 166 107
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t58 : ((-74035594347/2000000000000 : ℚ) : ℝ) ≤ stT166 58 := by
  have hc : ((-281919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74035594347/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-281919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c59 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-909/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -993111/2500000) (δ := 4213/500000000) (ψ := -123819/1000000) 166 108
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t59 : ((-237334547/100000000000 : ℚ) : ℝ) ≤ stT166 59 := by
  have hc : ((-1823/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237334547/100000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-1823/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c60 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((22589/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3002503/10000000) (δ := 8377/1000000000) (ψ := -123819/1000000) 166 108
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t60 : ((116632916439/2500000000000 : ℚ) : ℝ) ≤ stT166 60 := by
  have hc : ((180687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116632916439/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((180687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c61 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-173589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5845801/10000000) (δ := 8319/1000000000) (ψ := -123819/1000000) 166 109
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t61 : ((-444547957907/5000000000000 : ℚ) : ℝ) ≤ stT166 61 := by
  have hc : ((-347203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444547957907/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-347203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c62 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((935571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 902307/10000000) (δ := 2121/250000000) (ψ := -123819/1000000) 166 109
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t62 : ((1188112605521/10000000000000 : ℚ) : ℝ) ≤ stT166 62 := by
  have hc : ((935521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1188112605521/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((935521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c63 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-992247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7542473/10000000) (δ := 2121/250000000) (ψ := -123819/1000000) 166 109
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t63 : ((-625088564477/5000000000000 : ℚ) : ℝ) ≤ stT166 63 := by
  have hc : ((-992297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625088564477/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-992297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c64 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((158977/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -814973/5000000) (δ := 8391/1000000000) (ψ := -123819/1000000) 166 110
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t64 : ((158967/1600000 : ℚ) : ℝ) ≤ stT166 64 := by
  have hc : ((158967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158967/1600000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((158967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c65 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-85941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4804297/10000000) (δ := 8391/1000000000) (ψ := -123819/1000000) 166 110
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t65 : ((-53306125909/1250000000000 : ℚ) : ℝ) ≤ stT166 65 := by
  have hc : ((-171907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53306125909/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-171907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c66 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-25347/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2283827/5000000) (δ := 1661/200000000) (ψ := -123819/1000000) 166 111
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t66 : ((-780153927/25000000000 : ℚ) : ℝ) ≤ stT166 66 := by
  have hc : ((-3169/12500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-780153927/25000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-3169/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c67 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((7843/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66923/400000) (δ := 4249/500000000) (ψ := -123819/1000000) 166 111
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t67 : ((1916227039/20000000000 : ℚ) : ℝ) ≤ stT166 67 := by
  have hc : ((3137/4000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1916227039/20000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((3137/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c68 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-199983/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7821341/10000000) (δ := 1661/200000000) (ψ := -123819/1000000) 166 111
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t68 : ((-242527311247/2000000000000 : ℚ) : ℝ) ≤ stT166 68 := by
  have hc : ((-199993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242527311247/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-199993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c69 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((372171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45703/250000) (δ := 4203/500000000) (ψ := -123819/1000000) 166 112
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t69 : ((112002734817/1250000000000 : ℚ) : ℝ) ≤ stT166 69 := by
  have hc : ((186073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112002734817/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((186073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c70 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-21593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414319/1000000) (δ := 8397/1000000000) (ψ := -123819/1000000) 166 112
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t70 : ((-51647040319/5000000000000 : ℚ) : ℝ) ≤ stT166 70 := by
  have hc : ((-43211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51647040319/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-43211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c71 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-644577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1419541/2500000) (δ := 8313/1000000000) (ψ := -123819/1000000) 166 113
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t71 : ((-382515860157/5000000000000 : ℚ) : ℝ) ≤ stT166 71 := by
  have hc : ((-644627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382515860157/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-644627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c72 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((998727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2523/200000) (δ := 849/100000000) (ψ := -123819/1000000) 166 113
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t72 : ((1176951829947/10000000000000 : ℚ) : ℝ) ≤ stT166 72 := by
  have hc : ((998677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1176951829947/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((998677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c73 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-69567/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 585037/1000000) (δ := 8313/1000000000) (ψ := -123819/1000000) 166 113
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t73 : ((-5089243979/62500000000 : ℚ) : ℝ) ≤ stT166 73 := by
  have hc : ((-17393/25000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5089243979/62500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-17393/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c74 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-56733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4211269/10000000) (δ := 421/50000000) (ψ := -123819/1000000) 166 114
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t74 : ((-32989934783/2500000000000 : ℚ) : ℝ) ≤ stT166 74 := by
  have hc : ((-28379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32989934783/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-28379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c75 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((855787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359317/10000000) (δ := 8383/1000000000) (ψ := -123819/1000000) 166 114
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t75 : ((9881195139/100000000000 : ℚ) : ℝ) ≤ stT166 75 := by
  have hc : ((855737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9881195139/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((855737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c76 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-921387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274243/400000) (δ := 8383/1000000000) (ψ := -123819/1000000) 166 114
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t76 : ((-1056961032523/10000000000000 : ℚ) : ℝ) ≤ stT166 76 := by
  have hc : ((-921437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1056961032523/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-921437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c77 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((198679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3426967/10000000) (δ := 2119/250000000) (ψ := -123819/1000000) 166 115
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t77 : ((45271720309/2000000000000 : ℚ) : ℝ) ≤ stT166 77 := by
  have hc : ((198629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45271720309/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((198629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c78 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((71709/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 240993/1250000) (δ := 2119/250000000) (ψ := -123819/1000000) 166 115
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t78 : ((10148598751/125000000000 : ℚ) : ℝ) ≤ stT166 78 := by
  have hc : ((8963/12500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10148598751/125000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((8963/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c79 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-241869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7214629/10000000) (δ := 2119/250000000) (ψ := -123819/1000000) 166 115
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t79 : ((-17008623317/156250000000 : ℚ) : ℝ) ≤ stT166 79 := by
  have hc : ((-483763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17008623317/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-483763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c80 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((64643/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -818283/2500000) (δ := 8369/1000000000) (ψ := -123819/1000000) 166 116
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t80 : ((144518063613/5000000000000 : ℚ) : ℝ) ≤ stT166 80 := by
  have hc : ((129261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144518063613/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((129261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c81 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((729721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941103/5000000) (δ := 4217/500000000) (ψ := -123819/1000000) 166 116
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t81 : ((810745474481/10000000000000 : ℚ) : ℝ) ≤ stT166 81 := by
  have hc : ((729671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((810745474481/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((729671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c82 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-938729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6974297/10000000) (δ := 8369/1000000000) (ψ := -123819/1000000) 166 116
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t82 : ((-259177167541/2500000000000 : ℚ) : ℝ) ≤ stT166 82 := by
  have hc : ((-938779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259177167541/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-938779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c83 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((89363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -740657/2000000) (δ := 4171/500000000) (ψ := -123819/1000000) 166 117
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t83 : ((49016849973/5000000000000 : ℚ) : ℝ) ≤ stT166 83 := by
  have hc : ((89313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49016849973/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((89313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c84 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((437169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1266817/10000000) (δ := 16661/1000000000) (ψ := -123819/1000000) 166 117
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t84 : ((59620376227/625000000000 : ℚ) : ℝ) ≤ stT166 84 := by
  have hc : ((54643/62500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59620376227/625000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((54643/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c85 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-391803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3089057/5000000) (δ := 4171/500000000) (ψ := -123819/1000000) 166 117
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t85 : ((-106249353921/1250000000000 : ℚ) : ℝ) ≤ stT166 85 := by
  have hc : ((-97957/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106249353921/1250000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-97957/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c86 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-59029/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4676009/10000000) (δ := 8449/1000000000) (ψ := -123819/1000000) 166 118
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t86 : ((-7957925849/250000000000 : ℚ) : ℝ) ≤ stT166 86 := by
  have hc : ((-59039/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7957925849/250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-59039/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c87 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((499407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30441/2500000) (δ := 4177/500000000) (ψ := -123819/1000000) 166 118
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t87 : ((16731044837/156250000000 : ℚ) : ℝ) ≤ stT166 87 := by
  have hc : ((249691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16731044837/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((249691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c88 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-366341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194587/400000) (δ := 8449/1000000000) (ψ := -123819/1000000) 166 118
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t88 : ((-97643567891/2500000000000 : ℚ) : ℝ) ≤ stT166 88 := by
  have hc : ((-366391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97643567891/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-366391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c89 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-97197/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1538499/2500000) (δ := 2089/250000000) (ψ := -123819/1000000) 166 119
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t89 : ((-206070501187/2500000000000 : ℚ) : ℝ) ≤ stT166 89 := by
  have hc : ((-388813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206070501187/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-388813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c90 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((821459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1517077/10000000) (δ := 8447/1000000000) (ψ := -123819/1000000) 166 119
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t90 : ((216460163907/2500000000000 : ℚ) : ℝ) ≤ stT166 90 := by
  have hc : ((821409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216460163907/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((821409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c91 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((67329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3068611/10000000) (δ := 16647/1000000000) (ψ := -123819/1000000) 166 119
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t91 : ((17642357649/500000000000 : ℚ) : ℝ) ≤ stT166 91 := by
  have hc : ((67319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17642357649/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((67319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c92 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-248753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7604167/10000000) (δ := 2089/250000000) (ψ := -123819/1000000) 166 119
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t92 : ((-518712387263/5000000000000 : ℚ) : ℝ) ≤ stT166 92 := by
  have hc : ((-497531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-518712387263/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-497531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c93 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((12357/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3617273/10000000) (δ := 417/50000000) (ψ := -123819/1000000) 166 120
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t93 : ((200131543/15625000000 : ℚ) : ℝ) ≤ stT166 93 := by
  have hc : ((386/3125 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200131543/15625000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((386/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c94 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((236631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 821277/10000000) (δ := 8463/1000000000) (ψ := -123819/1000000) 166 120
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t94 : ((488106579777/5000000000000 : ℚ) : ℝ) ≤ stT166 94 := by
  have hc : ((473237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488106579777/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((473237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c95 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-491963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325803/625000) (δ := 417/50000000) (ψ := -123819/1000000) 166 120
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t95 : ((-504795005727/10000000000000 : ℚ) : ℝ) ≤ stT166 95 := by
  have hc : ((-492013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504795005727/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-492013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c96 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-776451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3074763/5000000) (δ := 8433/1000000000) (ψ := -123819/1000000) 166 121
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t96 : ((-792513227121/10000000000000 : ℚ) : ℝ) ≤ stT166 96 := by
  have hc : ((-776501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-792513227121/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-776501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c97 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((184687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462241/2500000) (δ := 8433/1000000000) (ψ := -123819/1000000) 166 121
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t97 : ((187508514877/2500000000000 : ℚ) : ℝ) ≤ stT166 97 := by
  have hc : ((369349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187508514877/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((369349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c98 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((114213/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 601871/2500000) (δ := 837/100000000) (ψ := -123819/1000000) 166 121
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t98 : ((14420298607/250000000000 : ℚ) : ℝ) ≤ stT166 98 := by
  have hc : ((114203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14420298607/250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((114203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c99 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-35231/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662073/1000000) (δ := 837/100000000) (ψ := -123819/1000000) 166 121
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t99 : ((-17705251927/200000000000 : ℚ) : ℝ) ≤ stT166 99 := by
  have hc : ((-35233/40000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17705251927/200000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-35233/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c100 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-192749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4916359/10000000) (δ := 4163/500000000) (ψ := -123819/1000000) 166 122
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t100 : ((-96387/2500000 : ℚ) : ℝ) ≤ stT166 100 := by
  have hc : ((-96387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96387/2500000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-96387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c101 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((190173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -786943/10000000) (δ := 4163/500000000) (ψ := -123819/1000000) 166 122
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t101 : ((189219221031/2000000000000 : ℚ) : ℝ) ≤ stT166 101 := by
  have hc : ((190163/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189219221031/2000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((190163/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c102 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((247493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1650881/5000000) (δ := 8477/1000000000) (ψ := -123819/1000000) 166 122
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t102 : ((245004944121/10000000000000 : ℚ) : ℝ) ≤ stT166 102 := by
  have hc : ((247443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245004944121/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((247443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c103 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-61237/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7350543/10000000) (δ := 4163/500000000) (ψ := -123819/1000000) 166 122
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t103 : ((-48273385893/500000000000 : ℚ) : ℝ) ≤ stT166 103 := by
  have hc : ((-489921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48273385893/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-489921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c104 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-167503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1086933/2500000) (δ := 4209/500000000) (ψ := -123819/1000000) 166 123
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t104 : ((-164299288293/10000000000000 : ℚ) : ℝ) ≤ stT166 104 := by
  have hc : ((-167553/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164299288293/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-167553/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c105 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((61793/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -376389/10000000) (δ := 1677/200000000) (ψ := -123819/1000000) 166 123
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t105 : ((4824059121/50000000000 : ℚ) : ℝ) ≤ stT166 105 := by
  have hc : ((494319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4824059121/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((494319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c106 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((147349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3557271/10000000) (δ := 4209/500000000) (ψ := -123819/1000000) 166 123
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t106 : ((28613861843/2000000000000 : ℚ) : ℝ) ≤ stT166 106 := by
  have hc : ((147299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28613861843/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((147299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c107 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-987231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3727019/5000000) (δ := 4209/500000000) (ψ := -123819/1000000) 166 123
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t107 : ((-954441072097/10000000000000 : ℚ) : ℝ) ≤ stT166 107 := by
  have hc : ((-987281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-954441072097/10000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-987281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c108 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-37099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4393429/10000000) (δ := 8311/1000000000) (ψ := -123819/1000000) 166 124
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t108 : ((-35708172359/2000000000000 : ℚ) : ℝ) ≤ stT166 108 := by
  have hc : ((-37109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35708172359/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-37109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c109 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((243563/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28427/500000) (δ := 8311/1000000000) (ψ := -123819/1000000) 166 124
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t109 : ((233279001213/2500000000000 : ℚ) : ℝ) ≤ stT166 109 := by
  have hc : ((487101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233279001213/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((487101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c110 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((139243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 402681/1250000) (δ := 2123/250000000) (ψ := -123819/1000000) 166 124
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t110 : ((33184768179/1250000000000 : ℚ) : ℝ) ≤ stT166 110 := by
  have hc : ((69609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33184768179/1250000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((69609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c111 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-469561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1744289/2500000) (δ := 8311/1000000000) (ψ := -123819/1000000) 166 124
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t111 : ((-111427827147/1250000000000 : ℚ) : ℝ) ≤ stT166 111 := by
  have hc : ((-234793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111427827147/1250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-234793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c112 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-419359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2504419/5000000) (δ := 8399/1000000000) (ψ := -123819/1000000) 166 125
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t112 : ((-24769037313/625000000000 : ℚ) : ℝ) ≤ stT166 112 := by
  have hc : ((-419409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24769037313/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-419409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c113 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((215959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1319903/10000000) (δ := 8399/1000000000) (ψ := -123819/1000000) 166 125
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t113 : ((5078629787/62500000000 : ℚ) : ℝ) ≤ stT166 113 := by
  have hc : ((431893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5078629787/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((431893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c114 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((297071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146031/625000) (δ := 8399/1000000000) (ψ := -123819/1000000) 166 125
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t114 : ((27820882791/500000000000 : ℚ) : ℝ) ≤ stT166 114 := by
  have hc : ((148523/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27820882791/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((148523/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c115 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-363381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5960981/10000000) (δ := 2101/250000000) (ψ := -123819/1000000) 166 125
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t115 : ((-33887791203/500000000000 : ℚ) : ℝ) ≤ stT166 115 := by
  have hc : ((-181703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33887791203/500000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-181703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c116 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-155511/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769239/1250000) (δ := 4153/500000000) (ψ := -123819/1000000) 166 126
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t116 : ((-144397671517/2000000000000 : ℚ) : ℝ) ≤ stT166 116 := by
  have hc : ((-155521/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144397671517/2000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-155521/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c117 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((509103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -518327/2000000) (δ := 4153/500000000) (ψ := -123819/1000000) 166 126
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t117 : ((941238997/20000000000 : ℚ) : ℝ) ≤ stT166 117 := by
  have hc : ((509053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((941238997/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((509053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c118 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((58131/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 188061/2000000) (δ := 8497/1000000000) (ψ := -123819/1000000) 166 126
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t118 : ((214044041601/2500000000000 : ℚ) : ℝ) ≤ stT166 118 := by
  have hc : ((465023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214044041601/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((465023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c119 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-204709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4442407/10000000) (δ := 8497/1000000000) (ψ := -123819/1000000) 166 126
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t119 : ((-187702370541/10000000000000 : ℚ) : ℝ) ≤ stT166 119 := by
  have hc : ((-204759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187702370541/10000000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-204759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c120 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-9997/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7792711/10000000) (δ := 8413/1000000000) (ψ := -123819/1000000) 166 127
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t120 : ((-3650571129/40000000000 : ℚ) : ℝ) ≤ stT166 120 := by
  have hc : ((-3999/4000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3650571129/40000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-3999/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c121 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-10493/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4348709/10000000) (δ := 8413/1000000000) (ψ := -123819/1000000) 166 127
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t121 : ((-76335462179/5000000000000 : ℚ) : ℝ) ≤ stT166 121 := by
  have hc : ((-83969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76335462179/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-83969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c122 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((465579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233263/2500000) (δ := 839/100000000) (ψ := -123819/1000000) 166 127
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t122 : ((210746286389/2500000000000 : ℚ) : ℝ) ≤ stT166 122 := by
  have hc : ((232777/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210746286389/2500000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((232777/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c123 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((277727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1227359/5000000) (δ := 8413/1000000000) (ψ := -123819/1000000) 166 127
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t123 : ((125197642319/2500000000000 : ℚ) : ℝ) ≤ stT166 123 := by
  have hc : ((138851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125197642319/2500000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((138851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c124 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-685453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363441/625000) (δ := 8413/1000000000) (ψ := -123819/1000000) 166 127
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t124 : ((-615600202581/10000000000000 : ℚ) : ℝ) ≤ stT166 124 := by
  have hc : ((-685503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615600202581/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-685503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c125 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-868923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1311909/2000000) (δ := 8483/1000000000) (ψ := -123819/1000000) 166 128
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t125 : ((-194308445611/2500000000000 : ℚ) : ℝ) ≤ stT166 125 := by
  have hc : ((-868973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194308445611/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-868973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c126 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((133221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1626371/5000000) (δ := 8483/1000000000) (ψ := -123819/1000000) 166 128
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t126 : ((2966508013/125000000000 : ℚ) : ℝ) ≤ stT166 126 := by
  have hc : ((33299/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2966508013/125000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((33299/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c127 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((499969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223/80000) (δ := 13/1562500) (ψ := -123819/1000000) 166 128
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t127 : ((13863384627/156250000000 : ℚ) : ℝ) ≤ stT166 127 := by
  have hc : ((62493/62500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13863384627/156250000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((62493/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c128 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((254833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3282803/10000000) (δ := 13/1562500) (ψ := -123819/1000000) 166 128
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t128 : ((225198362389/10000000000000 : ℚ) : ℝ) ≤ stT166 128 := by
  have hc : ((254783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225198362389/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((254783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c129 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-429719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 203513/312500) (δ := 13/1562500) (ψ := -123819/1000000) 166 128
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t129 : ((-23648033409/312500000000 : ℚ) : ℝ) ≤ stT166 129 := by
  have hc : ((-26859/31250 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23648033409/312500000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-26859/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c130 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-146987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5990917/10000000) (δ := 2107/250000000) (ψ := -123819/1000000) 166 129
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t130 : ((-128925041823/2000000000000 : ℚ) : ℝ) ≤ stT166 130 := by
  have hc : ((-146997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128925041823/2000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-146997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c131 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((86357/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1405407/5000000) (δ := 67/8000000) (ψ := -123819/1000000) 166 129
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t131 : ((9430214911/250000000000 : ℚ) : ℝ) ≤ stT166 131 := by
  have hc : ((86347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9430214911/250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((86347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c132 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((123811/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69019/2000000) (δ := 67/8000000) (ψ := -123819/1000000) 166 129
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t132 : ((107758168743/1250000000000 : ℚ) : ℝ) ≤ stT166 132 := by
  have hc : ((495219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107758168743/1250000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((495219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c133 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((89477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3477183/10000000) (δ := 67/8000000) (ψ := -123819/1000000) 166 129
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t133 : ((19391158567/1250000000000 : ℚ) : ℝ) ≤ stT166 133 := by
  have hc : ((22363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19391158567/1250000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((22363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c134 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-874073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6585803/10000000) (δ := 4157/250000000) (ψ := -123819/1000000) 166 129
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t134 : ((-755127761887/10000000000000 : ℚ) : ℝ) ≤ stT166 134 := by
  have hc : ((-874123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-755127761887/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-874123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c135 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-373609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -377291/625000) (δ := 1667/200000000) (ψ := -123819/1000000) 166 130
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t135 : ((-160786479671/2500000000000 : ℚ) : ℝ) ≤ stT166 135 := by
  have hc : ((-186817/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160786479671/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-186817/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c136 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((372063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -594783/2000000) (δ := 2117/250000000) (ψ := -123819/1000000) 166 130
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t136 : ((79749542849/2500000000000 : ℚ) : ℝ) ≤ stT166 136 := by
  have hc : ((372013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79749542849/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((372013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c137 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((999647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66417/10000000) (δ := 1667/200000000) (ψ := -123819/1000000) 166 130
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t137 : ((854012694129/10000000000000 : ℚ) : ℝ) ≤ stT166 137 := by
  have hc : ((999597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((854012694129/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((999597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c138 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((330621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3084587/10000000) (δ := 2117/250000000) (ψ := -123819/1000000) 166 130
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t138 : ((35175068397/1250000000000 : ℚ) : ℝ) ≤ stT166 138 := by
  have hc : ((330571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35175068397/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((330571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c139 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-758891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1520253/2500000) (δ := 1667/200000000) (ψ := -123819/1000000) 166 130
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t139 : ((-643725407849/10000000000000 : ℚ) : ℝ) ≤ stT166 139 := by
  have hc : ((-758941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-643725407849/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-758941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c140 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-886633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -831503/1250000) (δ := 8361/1000000000) (ψ := -123819/1000000) 166 131
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t140 : ((-149876914173/2000000000000 : ℚ) : ℝ) ≤ stT166 140 := by
  have hc : ((-886683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149876914173/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-886683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c141 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((22837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3698303/10000000) (δ := 8361/1000000000) (ψ := -123819/1000000) 166 131
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t141 : ((38443350999/5000000000000 : ℚ) : ℝ) ≤ stT166 141 := by
  have hc : ((45649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38443350999/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((45649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c142 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((119187/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153083/2000000) (δ := 8361/1000000000) (ψ := -123819/1000000) 166 131
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t142 : ((400056883863/5000000000000 : ℚ) : ℝ) ≤ stT166 142 := by
  have hc : ((476723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400056883863/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((476723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c143 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((32669/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2146889/10000000) (δ := 8361/1000000000) (ψ := -123819/1000000) 166 131
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t143 : ((27317099293/500000000000 : ℚ) : ℝ) ≤ stT166 143 := by
  have hc : ((65333/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27317099293/500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((65333/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c144 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-430229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519429/5000000) (δ := 8361/1000000000) (ψ := -123819/1000000) 166 131
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t144 : ((-179283060093/5000000000000 : ℚ) : ℝ) ≤ stT166 144 := by
  have hc : ((-430279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179283060093/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-430279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c145 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-999741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3898549/5000000) (δ := 4227/500000000) (ψ := -123819/1000000) 166 132
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t145 : ((-166056286981/2000000000000 : ℚ) : ℝ) ≤ stT166 145 := by
  have hc : ((-999791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166056286981/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-999791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c146 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-197993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1236211/2500000) (δ := 8349/1000000000) (ψ := -123819/1000000) 166 132
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t146 : ((-40970221227/1250000000000 : ℚ) : ℝ) ≤ stT166 146 := by
  have hc : ((-99009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40970221227/1250000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-99009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c147 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((165963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66003/312500) (δ := 4227/500000000) (ψ := -123819/1000000) 166 132
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t147 : ((136873649093/2500000000000 : ℚ) : ℝ) ≤ stT166 147 := by
  have hc : ((331901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136873649093/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((331901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c148 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((240223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17537/250000) (δ := 8349/1000000000) (ψ := -123819/1000000) 166 132
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t148 : ((197451589737/2500000000000 : ℚ) : ℝ) ≤ stT166 148 := by
  have hc : ((480421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197451589737/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((480421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c149 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((42873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3496131/10000000) (δ := 4227/500000000) (ψ := -123819/1000000) 166 132
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t149 : ((70225300551/5000000000000 : ℚ) : ℝ) ≤ stT166 149 := by
  have hc : ((85721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70225300551/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((85721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c150 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-161277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250881/400000) (δ := 8349/1000000000) (ψ := -123819/1000000) 166 132
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t150 : ((-131690351639/2000000000000 : ℚ) : ℝ) ≤ stT166 150 := by
  have hc : ((-161287/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131690351639/2000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-161287/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c151 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-222867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6678429/10000000) (δ := 1057/125000000) (ψ := -123819/1000000) 166 133
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t151 : ((-362753770851/5000000000000 : ℚ) : ℝ) ≤ stT166 151 := by
  have hc : ((-445759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362753770851/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-445759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c152 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-4859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3939139/10000000) (δ := 8347/1000000000) (ψ := -123819/1000000) 166 133
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t152 : ((-995432293/2500000000000 : ℚ) : ℝ) ≤ stT166 152 := by
  have hc : ((-4909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-995432293/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-4909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c153 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((883681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608909/5000000) (δ := 8347/1000000000) (ψ := -123819/1000000) 166 133
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t153 : ((178593312303/2500000000000 : ℚ) : ℝ) ≤ stT166 153 := by
  have hc : ((883631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178593312303/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((883631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c154 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((828533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1485783/10000000) (δ := 1057/125000000) (ψ := -123819/1000000) 166 133
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t154 : ((333804914013/5000000000000 : ℚ) : ℝ) ≤ stT166 154 := by
  have hc : ((828483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333804914013/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((828483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c155 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-19559/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417187/1000000) (δ := 8347/1000000000) (ψ := -123819/1000000) 166 133
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t155 : ((-785910609/100000000000 : ℚ) : ℝ) ≤ stT166 155 := by
  have hc : ((-19569/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-785910609/100000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-19569/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c156 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-459489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3420347/5000000) (δ := 1057/125000000) (ψ := -123819/1000000) 166 133
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t156 : ((-183952874237/2500000000000 : ℚ) : ℝ) ≤ stT166 156 := by
  have hc : ((-229757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183952874237/2500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-229757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c157 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-792809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6215503/10000000) (δ := 8439/1000000000) (ψ := -123819/1000000) 166 134
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t157 : ((-632770460733/10000000000000 : ℚ) : ℝ) ≤ stT166 157 := by
  have hc : ((-792859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-632770460733/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-792859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c158 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((138119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -716117/2000000) (δ := 8439/1000000000) (ψ := -123819/1000000) 166 134
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t158 : ((109841759433/10000000000000 : ℚ) : ℝ) ≤ stT166 158 := by
  have hc : ((138069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109841759433/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((138069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c159 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((926833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962267/10000000) (δ := 8439/1000000000) (ψ := -123819/1000000) 166 134
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t159 : ((734986184933/10000000000000 : ℚ) : ℝ) ≤ stT166 159 := by
  have hc : ((926783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((734986184933/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((926783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c160 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((198133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1639617/10000000) (δ := 8439/1000000000) (ψ := -123819/1000000) 166 134
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t160 : ((313255851129/5000000000000 : ℚ) : ℝ) ≤ stT166 160 := by
  have hc : ((396241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((313255851129/5000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((396241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c161 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-119031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169011/400000) (δ := 2091/250000000) (ψ := -123819/1000000) 166 134
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t161 : ((-93849045991/10000000000000 : ℚ) : ℝ) ≤ stT166 161 := by
  have hc : ((-119081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93849045991/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-119081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c162 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-911611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1358991/2000000) (δ := 2091/250000000) (ψ := -123819/1000000) 166 134
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t162 : ((-28650770247/400000000000 : ℚ) : ℝ) ≤ stT166 162 := by
  have hc : ((-911661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28650770247/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-911661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c163 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-826499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317957/500000) (δ := 2083/250000000) (ψ := -123819/1000000) 166 135
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t163 : ((-647403596289/10000000000000 : ℚ) : ℝ) ≤ stT166 163 := by
  have hc : ((-826549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-647403596289/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-826549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c164 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((42417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3820917/10000000) (δ := 2083/250000000) (ψ := -123819/1000000) 166 135
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t164 : ((8270758639/2500000000000 : ℚ) : ℝ) ≤ stT166 164 := by
  have hc : ((42367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8270758639/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((42367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c165 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((86819/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -324533/2500000) (δ := 2083/250000000) (ψ := -123819/1000000) 166 135
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t165 : ((16896131343/250000000000 : ℚ) : ℝ) ≤ stT166 165 := by
  have hc : ((43407/50000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16896131343/250000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((43407/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c166 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((13832/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1209423/10000000) (δ := 8471/1000000000) (ψ := -123819/1000000) 166 135
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t166 : ((6870464277/100000000000 : ℚ) : ℝ) ≤ stT166 166 := by
  have hc : ((442599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6870464277/100000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((442599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c167 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((89893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1850977/5000000) (δ := 2083/250000000) (ψ := -123819/1000000) 166 135
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t167 : ((69522579789/10000000000000 : ℚ) : ℝ) ≤ stT166 167 := by
  have hc : ((89843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69522579789/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((89843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c168 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-391981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3089773/5000000) (δ := 8471/1000000000) (ψ := -123819/1000000) 166 135
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t168 : ((-151219646551/2500000000000 : ℚ) : ℝ) ≤ stT166 168 := by
  have hc : ((-196003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151219646551/2500000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-196003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c169 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-59417/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1766369/2500000) (δ := 337/40000000) (ψ := -123819/1000000) 166 136
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t169 : ((-365662417391/5000000000000 : ℚ) : ℝ) ≤ stT166 169 := by
  have hc : ((-475361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-365662417391/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-475361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c170 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-272551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46171/100000) (δ := 4189/500000000) (ψ := -123819/1000000) 166 136
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t170 : ((-41815085193/2000000000000 : ℚ) : ℝ) ≤ stT166 170 := by
  have hc : ((-272601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41815085193/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-272601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c171 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((40147/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -545771/2500000) (δ := 337/40000000) (ψ := -123819/1000000) 166 136
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t171 : ((245590271569/5000000000000 : ℚ) : ℝ) ≤ stT166 171 := by
  have hc : ((321151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245590271569/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((321151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c172 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((3111/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11837/500000) (δ := 4189/500000000) (ψ := -123819/1000000) 166 136
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t172 : ((18975947781/250000000000 : ℚ) : ℝ) ≤ stT166 172 := by
  have hc : ((99547/100000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18975947781/250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((99547/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c173 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((245737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 330317/1250000) (δ := 337/40000000) (ψ := -123819/1000000) 166 136
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t173 : ((2335139349/62500000000 : ℚ) : ℝ) ≤ stT166 173 := by
  have hc : ((15357/31250 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2335139349/62500000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((15357/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c174 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-85729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 629309/1250000) (δ := 4189/500000000) (ψ := -123819/1000000) 166 136
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t174 : ((-64998650161/2000000000000 : ℚ) : ℝ) ≤ stT166 174 := by
  have hc : ((-85739/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64998650161/2000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-85739/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c175 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-984463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926589/1250000) (δ := 337/40000000) (ψ := -123819/1000000) 166 136
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t175 : ((-744221927577/10000000000000 : ℚ) : ℝ) ≤ stT166 175 := by
  have hc : ((-984513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-744221927577/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-984513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c176 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-179589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5930581/10000000) (δ := 4159/500000000) (ψ := -123819/1000000) 166 137
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t176 : ((-270759678137/5000000000000 : ℚ) : ℝ) ≤ stT166 176 := by
  have hc : ((-359203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270759678137/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-359203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c177 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((138639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1789637/5000000) (δ := 4159/500000000) (ψ := -123819/1000000) 166 137
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t177 : ((52084933747/5000000000000 : ℚ) : ℝ) ≤ stT166 177 := by
  have hc : ((138589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52084933747/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((138589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c178 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((109907/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1241247/10000000) (δ := 4159/500000000) (ψ := -123819/1000000) 166 137
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t178 : ((329496076193/5000000000000 : ℚ) : ℝ) ≤ stT166 178 := by
  have hc : ((439603/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329496076193/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((439603/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c179 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((226877/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270927/2500000) (δ := 1697/200000000) (ψ := -123819/1000000) 166 137
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t179 : ((67826587023/1000000000000 : ℚ) : ℝ) ≤ stT166 179 := by
  have hc : ((453729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67826587023/1000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((453729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c180 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((210931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3395673/10000000) (δ := 1697/200000000) (ψ := -123819/1000000) 166 137
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t180 : ((31436241551/2000000000000 : ℚ) : ℝ) ≤ stT166 180 := by
  have hc : ((210881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31436241551/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((210881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c181 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-649667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 711857/1250000) (δ := 1697/200000000) (ψ := -123819/1000000) 166 137
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t181 : ((-96586279503/2000000000000 : ℚ) : ℝ) ≤ stT166 181 := by
  have hc : ((-649717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96586279503/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-649717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c182 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-998703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241457/312500) (δ := 8411/1000000000) (ψ := -123819/1000000) 166 138
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t182 : ((-592260529/8000000000 : ℚ) : ℝ) ≤ stT166 182 := by
  have hc : ((-998753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592260529/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-998753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c183 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-573077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5452631/10000000) (δ := 1049/125000000) (ψ := -123819/1000000) 166 138
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t183 : ((-211834043597/5000000000000 : ℚ) : ℝ) ≤ stT166 183 := by
  have hc : ((-573127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211834043597/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-573127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c184 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((9067/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3191047/10000000) (δ := 1049/125000000) (ψ := -123819/1000000) 166 138
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t184 : ((106929953823/5000000000000 : ℚ) : ℝ) ≤ stT166 184 := by
  have hc : ((145047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106929953823/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((145047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c185 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((92989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -470853/5000000) (δ := 8411/1000000000) (ψ := -123819/1000000) 166 138
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t185 : ((4272696161/62500000000 : ℚ) : ℝ) ≤ stT166 185 := by
  have hc : ((11623/12500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4272696161/62500000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((11623/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c186 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((868717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323869/2500000) (δ := 8411/1000000000) (ψ := -123819/1000000) 166 138
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t186 : ((127387409549/2000000000000 : ℚ) : ℝ) ≤ stT166 186 := by
  have hc : ((868667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127387409549/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((868667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c187 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((809/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1760353/5000000) (δ := 8411/1000000000) (ψ := -123819/1000000) 166 138
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t187 : ((59141623/5000000000 : ℚ) : ℝ) ≤ stT166 187 := by
  have hc : ((647/4000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59141623/5000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((647/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c188 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-330749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2867013/5000000) (δ := 1049/125000000) (ψ := -123819/1000000) 166 138
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t188 : ((-4824834951/100000000000 : ℚ) : ℝ) ≤ stT166 188 := by
  have hc : ((-165387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4824834951/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-165387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c189 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-999467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7772321/10000000) (δ := 519/62500000) (ψ := -123819/1000000) 166 139
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t189 : ((-727041669181/10000000000000 : ℚ) : ℝ) ≤ stT166 189 := by
  have hc : ((-999517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-727041669181/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-999517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c190 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-307407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2791183/5000000) (δ := 519/62500000) (ψ := -123819/1000000) 166 139
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t190 : ((-27879355633/625000000000 : ℚ) : ℝ) ≤ stT166 190 := by
  have hc : ((-38429/62500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27879355633/625000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-38429/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c191 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((207727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -680773/2000000) (δ := 519/62500000) (ψ := -123819/1000000) 166 139
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t191 : ((75134838799/5000000000000 : ℚ) : ℝ) ≤ stT166 191 := by
  have hc : ((207677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75134838799/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((207677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c192 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((440053/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154597/1250000) (δ := 8499/1000000000) (ψ := -123819/1000000) 166 139
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t192 : ((79390621809/1250000000000 : ℚ) : ℝ) ≤ stT166 192 := by
  have hc : ((110007/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79390621809/1250000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((110007/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c193 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((933183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 459533/5000000) (δ := 8499/1000000000) (ψ := -123819/1000000) 166 139
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t193 : ((134336626079/2000000000000 : ℚ) : ℝ) ≤ stT166 193 := by
  have hc : ((933133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134336626079/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((933133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c194 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((169231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1531893/5000000) (δ := 8499/1000000000) (ψ := -123819/1000000) 166 139
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t194 : ((30370700337/1250000000000 : ℚ) : ℝ) ≤ stT166 194 := by
  have hc : ((84603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30370700337/1250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((84603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c195 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-486597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5197467/10000000) (δ := 8499/1000000000) (ψ := -123819/1000000) 166 139
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t195 : ((-69699043281/2000000000000 : ℚ) : ℝ) ≤ stT166 195 := by
  have hc : ((-486647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69699043281/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-486647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c196 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-195459/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7320233/10000000) (δ := 519/62500000) (ψ := -123819/1000000) 166 139
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t196 : ((-69810385067/1000000000000 : ℚ) : ℝ) ≤ stT166 196 := by
  have hc : ((-195469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69810385067/1000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-195469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c197 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-403633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3137877/5000000) (δ := 2099/250000000) (ψ := -123819/1000000) 166 140
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t197 : ((-143797309459/2500000000000 : ℚ) : ℝ) ≤ stT166 197 := by
  have hc : ((-201829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143797309459/2500000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-201829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c198 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-24709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1043621/2500000) (δ := 8407/1000000000) (ψ := -123819/1000000) 166 140
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t198 : ((-3513765681/500000000000 : ℚ) : ℝ) ≤ stT166 198 := by
  have hc : ((-49443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3513765681/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-49443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c199 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((26891/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2083797/10000000) (δ := 8407/1000000000) (ψ := -123819/1000000) 166 140
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t199 : ((19061101209/400000000000 : ℚ) : ℝ) ≤ stT166 199 := by
  have hc : ((26889/40000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19061101209/400000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((26889/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c200 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -361/1000000) (δ := 2099/250000000) (ψ := -123819/1000000) 166 140
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t200 : ((353534968797/5000000000000 : ℚ) : ℝ) ≤ stT166 200 := by
  have hc : ((999949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353534968797/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((999949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c201 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((42341/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 516561/2500000) (δ := 2099/250000000) (ψ := -123819/1000000) 166 140
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t201 : ((47780493507/1000000000000 : ℚ) : ℝ) ≤ stT166 201 := by
  have hc : ((338703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47780493507/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((338703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c202 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-39713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 825153/2000000) (δ := 8407/1000000000) (ψ := -123819/1000000) 166 140
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t202 : ((-6989894331/1250000000000 : ℚ) : ℝ) ≤ stT166 202 := by
  have hc : ((-19869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6989894331/1250000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-19869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c203 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-782871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6175159/10000000) (δ := 2099/250000000) (ψ := -123819/1000000) 166 140
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t203 : ((-549503281823/10000000000000 : ℚ) : ℝ) ≤ stT166 203 := by
  have hc : ((-782921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549503281823/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-782921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c204 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-494811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3746747/5000000) (δ := 4157/500000000) (ψ := -123819/1000000) 166 141
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t204 : ((-86613742969/1250000000000 : ℚ) : ℝ) ≤ stT166 204 := by
  have hc : ((-123709/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86613742969/1250000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-123709/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c205 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-115369/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341509/625000) (δ := 4157/500000000) (ψ := -123819/1000000) 166 141
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t205 : ((-80584270349/2000000000000 : ℚ) : ℝ) ≤ stT166 205 := by
  have hc : ((-115379/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80584270349/2000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-115379/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c206 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((191733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3444671/10000000) (δ := 4157/500000000) (ψ := -123819/1000000) 166 141
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t206 : ((133551871639/10000000000000 : ℚ) : ℝ) ≤ stT166 206 := by
  have hc : ((191683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133551871639/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((191683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c207 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((839737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89687/625000) (δ := 4157/500000000) (ψ := -123819/1000000) 166 141
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t207 : ((72952846247/1250000000000 : ℚ) : ℝ) ≤ stT166 207 := by
  have hc : ((839687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72952846247/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((839687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c208 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((974569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565017/10000000) (δ := 8489/1000000000) (ψ := -123819/1000000) 166 141
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t208 : ((5405656893/80000000000 : ℚ) : ℝ) ≤ stT166 208 := by
  have hc : ((974519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5405656893/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((974519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c209 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((521511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31943/125000) (δ := 8489/1000000000) (ψ := -123819/1000000) 166 141
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t209 : ((180350937077/5000000000000 : ℚ) : ℝ) ≤ stT166 209 := by
  have hc : ((521461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180350937077/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((521461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c210 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-241341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113409/250000) (δ := 4157/500000000) (ψ := -123819/1000000) 166 141
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t210 : ((-83287860903/5000000000000 : ℚ) : ℝ) ≤ stT166 210 := by
  have hc : ((-241391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83287860903/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-241391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c211 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-171701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6507859/10000000) (δ := 4157/500000000) (ψ := -123819/1000000) 166 141
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t211 : ((-118210832019/2000000000000 : ℚ) : ℝ) ≤ stT166 211 := by
  have hc : ((-171711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118210832019/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-171711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c212 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-969793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7237943/10000000) (δ := 4191/500000000) (ψ := -123819/1000000) 166 142
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t212 : ((-666091081929/10000000000000 : ℚ) : ℝ) ≤ stT166 212 := by
  have hc : ((-969843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-666091081929/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-969843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c213 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-516879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2642497/5000000) (δ := 8421/1000000000) (ψ := -123819/1000000) 166 142
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t213 : ((-354194064581/10000000000000 : ℚ) : ℝ) ≤ stT166 213 := by
  have hc : ((-516929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354194064581/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-516929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c214 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((232187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417647/1250000) (δ := 4191/500000000) (ψ := -123819/1000000) 166 142
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t214 : ((31737074229/2000000000000 : ℚ) : ℝ) ≤ stT166 214 := by
  have hc : ((232137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31737074229/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((232137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c215 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((845883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703223/5000000) (δ := 4191/500000000) (ψ := -123819/1000000) 166 142
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t215 : ((288426515501/5000000000000 : ℚ) : ℝ) ≤ stT166 215 := by
  have hc : ((845833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288426515501/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((845833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c216 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((489251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12983/250000) (δ := 4191/500000000) (ψ := -123819/1000000) 166 142
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t216 : ((166437865169/2500000000000 : ℚ) : ℝ) ≤ stT166 216 := by
  have hc : ((244613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166437865169/2500000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((244613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c217 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((56161/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609041/2500000) (δ := 8421/1000000000) (ψ := -123819/1000000) 166 142
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t217 : ((2382572729/62500000000 : ℚ) : ℝ) ≤ stT166 217 := by
  have hc : ((14039/25000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2382572729/62500000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((14039/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c218 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-83057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4344209/10000000) (δ := 4191/500000000) (ψ := -123819/1000000) 166 142
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t218 : ((-14067568863/1250000000000 : ℚ) : ℝ) ≤ stT166 218 := by
  have hc : ((-41541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14067568863/1250000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-41541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c219 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-399797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 312177/500000) (δ := 8421/1000000000) (ψ := -123819/1000000) 166 142
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t219 : ((-67543729659/1250000000000 : ℚ) : ℝ) ≤ stT166 219 := by
  have hc : ((-199911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67543729659/1250000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-199911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c220 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-39749/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7573767/10000000) (δ := 339/40000000) (ψ := -123819/1000000) 166 143
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t220 : ((-134000621/2000000000 : ℚ) : ℝ) ≤ stT166 220 := by
  have hc : ((-39751/40000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134000621/2000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-39751/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c221 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-324347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5691659/10000000) (δ := 339/40000000) (ψ := -123819/1000000) 166 143
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t221 : ((-54549071589/1250000000000 : ℚ) : ℝ) ≤ stT166 221 := by
  have hc : ((-81093/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54549071589/1250000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-81093/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c222 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((43543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38181/100000) (δ := 339/40000000) (ψ := -123819/1000000) 166 143
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t222 : ((7297646977/2500000000000 : ℚ) : ℝ) ≤ stT166 222 := by
  have hc : ((43493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7297646977/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((43493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c223 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((71009/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488231/2500000) (δ := 339/40000000) (ψ := -123819/1000000) 166 143
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t223 : ((11886939399/250000000000 : ℚ) : ℝ) ≤ stT166 223 := by
  have hc : ((17751/25000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11886939399/250000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((17751/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c224 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((999261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96089/10000000) (δ := 1041/125000000) (ψ := -123819/1000000) 166 143
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t224 : ((667625827283/10000000000000 : ℚ) : ℝ) ≤ stT166 224 := by
  have hc : ((999211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667625827283/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((999211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c225 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((764201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1752487/10000000) (δ := 1041/125000000) (ψ := -123819/1000000) 166 143
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t225 : ((254716745283/5000000000000 : ℚ) : ℝ) ≤ stT166 225 := by
  have hc : ((764151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254716745283/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((764151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c226 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((133269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143713/400000) (δ := 667/40000000) (ψ := -123819/1000000) 166 143
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t226 : ((8861594661/1000000000000 : ℚ) : ℝ) ≤ stT166 226 := by
  have hc : ((133219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8861594661/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((133219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c227 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-564009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5425071/10000000) (δ := 1041/125000000) (ψ := -123819/1000000) 166 143
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t227 : ((-93594873929/2500000000000 : ℚ) : ℝ) ≤ stT166 227 := by
  have hc : ((-564059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93594873929/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-564059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c228 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-485443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1449849/2000000) (δ := 1041/125000000) (ψ := -123819/1000000) 166 143
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t228 : ((-80377358989/1250000000000 : ℚ) : ℝ) ≤ stT166 228 := by
  have hc : ((-121367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80377358989/1250000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-121367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c229 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-884867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415157/625000) (δ := 1687/200000000) (ψ := -123819/1000000) 166 144
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t229 : ((-584769967023/10000000000000 : ℚ) : ℝ) ≤ stT166 229 := by
  have hc : ((-884917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584769967023/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-884917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c230 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-44373/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4834233/10000000) (δ := 523/62500000) (ψ := -123819/1000000) 166 144
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t230 : ((-117051336977/5000000000000 : ℚ) : ℝ) ≤ stT166 230 := by
  have hc : ((-177517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117051336977/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-177517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c231 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((13989/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3033797/10000000) (δ := 523/62500000) (ψ := -123819/1000000) 166 144
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t231 : ((9202760637/400000000000 : ℚ) : ℝ) ≤ stT166 231 := by
  have hc : ((13987/40000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9202760637/400000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((13987/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c232 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((109909/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1241163/10000000) (δ := 523/62500000) (ψ := -123819/1000000) 166 144
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t232 : ((72154672263/1250000000000 : ℚ) : ℝ) ≤ stT166 232 := by
  have hc : ((439611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72154672263/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((439611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c233 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((244109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271897/5000000) (δ := 1687/200000000) (ψ := -123819/1000000) 166 144
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t233 : ((319825486353/5000000000000 : ℚ) : ℝ) ≤ stT166 233 := by
  have hc : ((488193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319825486353/5000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((488193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c234 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((599079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160557/5000000) (δ := 523/62500000) (ψ := -123819/1000000) 166 144
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t234 : ((9789930947/250000000000 : ℚ) : ℝ) ≤ stT166 234 := by
  have hc : ((599029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9789930947/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((599029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c235 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-65493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102271/250000) (δ := 523/62500000) (ψ := -123819/1000000) 166 144
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t235 : ((-42755599647/10000000000000 : ℚ) : ℝ) ≤ stT166 235 := by
  have hc : ((-65543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42755599647/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-65543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c236 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-696441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1170611/2000000) (δ := 1687/200000000) (ψ := -123819/1000000) 166 144
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t236 : ((-90675466799/2000000000000 : ℚ) : ℝ) ≤ stT166 236 := by
  have hc : ((-696491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90675466799/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-696491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c237 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-199031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7607799/10000000) (δ := 523/62500000) (ψ := -123819/1000000) 166 144
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t237 : ((-12929106237/200000000000 : ℚ) : ℝ) ≤ stT166 237 := by
  have hc : ((-199041/200000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12929106237/200000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-199041/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c238 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-82507/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6352807/10000000) (δ := 423/50000000) (ψ := -123819/1000000) 166 145
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t238 : ((-835697007/15625000000 : ℚ) : ℝ) ≤ stT166 238 := by
  have hc : ((-5157/6250 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-835697007/15625000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-5157/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c239 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-135439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4612753/10000000) (δ := 8343/1000000000) (ψ := -123819/1000000) 166 145
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t239 : ((-10953060251/625000000000 : ℚ) : ℝ) ≤ stT166 239 := by
  have hc : ((-16933/62500 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10953060251/625000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-16933/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c240 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((16267/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1439981/5000000) (δ := 8343/1000000000) (ψ := -123819/1000000) 166 145
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t240 : ((2099801741/80000000000 : ℚ) : ℝ) ≤ stT166 240 := by
  have hc : ((3253/8000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2099801741/80000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((3253/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c241 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((895271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144299/1250000) (δ := 8343/1000000000) (ψ := -123819/1000000) 166 145
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t241 : ((144165494619/2500000000000 : ℚ) : ℝ) ≤ stT166 241 := by
  have hc : ((895221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144165494619/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((895221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c242 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((15229/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14101/250000) (δ := 8343/1000000000) (ψ := -123819/1000000) 166 145
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t242 : ((39156257959/625000000000 : ℚ) : ℝ) ≤ stT166 242 := by
  have hc : ((487303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39156257959/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((487303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c243 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((613627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18203/80000) (δ := 423/50000000) (ψ := -123819/1000000) 166 145
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t243 : ((787219291/20000000000 : ℚ) : ℝ) ≤ stT166 243 := by
  have hc : ((613577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((787219291/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((613577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c244 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-21081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3979697/10000000) (δ := 423/50000000) (ψ := -123819/1000000) 166 145
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t244 : ((-2705549847/2000000000000 : ℚ) : ℝ) ≤ stT166 244 := by
  have hc : ((-21131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2705549847/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-21131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c245 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-644229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5677027/10000000) (δ := 16743/1000000000) (ψ := -123819/1000000) 166 145
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t245 : ((-411615034683/10000000000000 : ℚ) : ℝ) ≤ stT166 245 := by
  have hc : ((-644279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411615034683/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-644279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c246 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-245281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7367467/10000000) (δ := 8343/1000000000) (ψ := -123819/1000000) 166 145
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t246 : ((-312786987699/5000000000000 : ℚ) : ℝ) ≤ stT166 246 := by
  have hc : ((-490587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-312786987699/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-490587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c247 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-443769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1664231/2500000) (δ := 169/20000000) (ψ := -123819/1000000) 166 146
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t247 : ((-28237946529/500000000000 : ℚ) : ℝ) ≤ stT166 247 := by
  have hc : ((-221897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28237946529/500000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-221897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c248 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-408917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2490079/5000000) (δ := 169/20000000) (ψ := -123819/1000000) 166 146
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t248 : ((-259694453967/10000000000000 : ℚ) : ℝ) ≤ stT166 248 := by
  have hc : ((-408967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259694453967/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-408967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c249 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((122119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3310157/10000000) (δ := 8353/1000000000) (ψ := -123819/1000000) 166 146
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t249 : ((9671737257/625000000000 : ℚ) : ℝ) ≤ stT166 249 := by
  have hc : ((61047/250000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9671737257/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((61047/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_c250 :
    |Real.cos (((166 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((395389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -329359/2000000) (δ := 169/20000000) (ψ := -123819/1000000) 166 146
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st166_t250 : ((12502496931/250000000000 : ℚ) : ℝ) ≤ stT166 250 := by
  have hc : ((98841/125000 : ℚ) : ℝ)
      ≤ Real.cos (((166 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st166_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12502496931/250000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((98841/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st166_p1 : ((496147/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT166 (i+1) := by
  rw [Finset.sum_range_one]
  exact st166_t1

theorem st166_p2 : ((1605172379269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT166 (i+1))
      = (∑ i ∈ Finset.range 1, stT166 (i+1)) + stT166 2 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 1
    simpa using h
  have hprev := st166_p1
  have hstep := st166_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p3 : ((1196733330299/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT166 (i+1))
      = (∑ i ∈ Finset.range 2, stT166 (i+1)) + stT166 3 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 2
    simpa using h
  have hprev := st166_p2
  have hstep := st166_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p4 : ((1781581538221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT166 (i+1))
      = (∑ i ∈ Finset.range 3, stT166 (i+1)) + stT166 4 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 3
    simpa using h
  have hprev := st166_p3
  have hstep := st166_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p5 : ((4580324543033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT166 (i+1))
      = (∑ i ∈ Finset.range 4, stT166 (i+1)) + stT166 5 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 4
    simpa using h
  have hprev := st166_p4
  have hstep := st166_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p6 : ((405553675443/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT166 (i+1))
      = (∑ i ∈ Finset.range 5, stT166 (i+1)) + stT166 6 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 5
    simpa using h
  have hprev := st166_p5
  have hstep := st166_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p7 : ((-278689065629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT166 (i+1))
      = (∑ i ∈ Finset.range 6, stT166 (i+1)) + stT166 7 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 6
    simpa using h
  have hprev := st166_p6
  have hstep := st166_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p8 : ((2019348108227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT166 (i+1))
      = (∑ i ∈ Finset.range 7, stT166 (i+1)) + stT166 8 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 7
    simpa using h
  have hprev := st166_p7
  have hstep := st166_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p9 : ((1259341118273/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT166 (i+1))
      = (∑ i ∈ Finset.range 8, stT166 (i+1)) + stT166 9 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 8
    simpa using h
  have hprev := st166_p8
  have hstep := st166_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p10 : ((3474768227003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT166 (i+1))
      = (∑ i ∈ Finset.range 9, stT166 (i+1)) + stT166 10 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 9
    simpa using h
  have hprev := st166_p9
  have hstep := st166_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p11 : ((486574895701/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT166 (i+1))
      = (∑ i ∈ Finset.range 10, stT166 (i+1)) + stT166 11 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 10
    simpa using h
  have hprev := st166_p10
  have hstep := st166_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p12 : ((347880895861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT166 (i+1))
      = (∑ i ∈ Finset.range 11, stT166 (i+1)) + stT166 12 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 11
    simpa using h
  have hprev := st166_p11
  have hstep := st166_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p13 : ((408286616461/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT166 (i+1))
      = (∑ i ∈ Finset.range 12, stT166 (i+1)) + stT166 13 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 12
    simpa using h
  have hprev := st166_p12
  have hstep := st166_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p14 : ((3962943346687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT166 (i+1))
      = (∑ i ∈ Finset.range 13, stT166 (i+1)) + stT166 14 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 13
    simpa using h
  have hprev := st166_p13
  have hstep := st166_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p15 : ((399326737741/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT166 (i+1))
      = (∑ i ∈ Finset.range 14, stT166 (i+1)) + stT166 15 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 14
    simpa using h
  have hprev := st166_p14
  have hstep := st166_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p16 : ((636265910527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT166 (i+1))
      = (∑ i ∈ Finset.range 15, stT166 (i+1)) + stT166 16 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 15
    simpa using h
  have hprev := st166_p15
  have hstep := st166_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p17 : ((1479638590441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT166 (i+1))
      = (∑ i ∈ Finset.range 16, stT166 (i+1)) + stT166 17 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 16
    simpa using h
  have hprev := st166_p16
  have hstep := st166_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p18 : ((1215629347241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT166 (i+1))
      = (∑ i ∈ Finset.range 17, stT166 (i+1)) + stT166 18 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 17
    simpa using h
  have hprev := st166_p17
  have hstep := st166_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p19 : ((2072909935001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT166 (i+1))
      = (∑ i ∈ Finset.range 18, stT166 (i+1)) + stT166 19 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 18
    simpa using h
  have hprev := st166_p18
  have hstep := st166_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p20 : ((63950662489/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT166 (i+1))
      = (∑ i ∈ Finset.range 19, stT166 (i+1)) + stT166 20 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 19
    simpa using h
  have hprev := st166_p19
  have hstep := st166_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p21 : ((1101360345377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT166 (i+1))
      = (∑ i ∈ Finset.range 20, stT166 (i+1)) + stT166 21 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 20
    simpa using h
  have hprev := st166_p20
  have hstep := st166_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p22 : ((244512726201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT166 (i+1))
      = (∑ i ∈ Finset.range 21, stT166 (i+1)) + stT166 22 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 21
    simpa using h
  have hprev := st166_p21
  have hstep := st166_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p23 : ((1559227295361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT166 (i+1))
      = (∑ i ∈ Finset.range 22, stT166 (i+1)) + stT166 23 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 22
    simpa using h
  have hprev := st166_p22
  have hstep := st166_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p24 : ((897183300213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT166 (i+1))
      = (∑ i ∈ Finset.range 23, stT166 (i+1)) + stT166 24 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 23
    simpa using h
  have hprev := st166_p23
  have hstep := st166_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p25 : ((1360283300213/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT166 (i+1))
      = (∑ i ∈ Finset.range 24, stT166 (i+1)) + stT166 25 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 24
    simpa using h
  have hprev := st166_p24
  have hstep := st166_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p26 : ((1761023016631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT166 (i+1))
      = (∑ i ∈ Finset.range 25, stT166 (i+1)) + stT166 26 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 25
    simpa using h
  have hprev := st166_p25
  have hstep := st166_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p27 : ((2159276159881/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT166 (i+1))
      = (∑ i ∈ Finset.range 26, stT166 (i+1)) + stT166 27 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 26
    simpa using h
  have hprev := st166_p26
  have hstep := st166_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p28 : ((5206300928817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT166 (i+1))
      = (∑ i ∈ Finset.range 27, stT166 (i+1)) + stT166 28 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 27
    simpa using h
  have hprev := st166_p27
  have hstep := st166_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p29 : ((12258530127673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT166 (i+1))
      = (∑ i ∈ Finset.range 28, stT166 (i+1)) + stT166 29 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 28
    simpa using h
  have hprev := st166_p28
  have hstep := st166_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p30 : ((13576634797069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT166 (i+1))
      = (∑ i ∈ Finset.range 29, stT166 (i+1)) + stT166 30 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 29
    simpa using h
  have hprev := st166_p29
  have hstep := st166_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p31 : ((13516632225037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT166 (i+1))
      = (∑ i ∈ Finset.range 30, stT166 (i+1)) + stT166 31 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 30
    simpa using h
  have hprev := st166_p30
  have hstep := st166_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p32 : ((5993218599967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT166 (i+1))
      = (∑ i ∈ Finset.range 31, stT166 (i+1)) + stT166 32 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 31
    simpa using h
  have hprev := st166_p31
  have hstep := st166_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p33 : ((41410719809/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT166 (i+1))
      = (∑ i ∈ Finset.range 32, stT166 (i+1)) + stT166 33 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 32
    simpa using h
  have hprev := st166_p32
  have hstep := st166_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p34 : ((1410063946133/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT166 (i+1))
      = (∑ i ∈ Finset.range 33, stT166 (i+1)) + stT166 34 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 33
    simpa using h
  have hprev := st166_p33
  have hstep := st166_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p35 : ((3222820531531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT166 (i+1))
      = (∑ i ∈ Finset.range 34, stT166 (i+1)) + stT166 35 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 34
    simpa using h
  have hprev := st166_p34
  have hstep := st166_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p36 : ((6164676006869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT166 (i+1))
      = (∑ i ∈ Finset.range 35, stT166 (i+1)) + stT166 36 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 35
    simpa using h
  have hprev := st166_p35
  have hstep := st166_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p37 : ((5446441435719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT166 (i+1))
      = (∑ i ∈ Finset.range 36, stT166 (i+1)) + stT166 37 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 36
    simpa using h
  have hprev := st166_p36
  have hstep := st166_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p38 : ((1204909643337/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT166 (i+1))
      = (∑ i ∈ Finset.range 37, stT166 (i+1)) + stT166 38 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 37
    simpa using h
  have hprev := st166_p37
  have hstep := st166_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p39 : ((1579789174727/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT166 (i+1))
      = (∑ i ∈ Finset.range 38, stT166 (i+1)) + stT166 39 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 38
    simpa using h
  have hprev := st166_p38
  have hstep := st166_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p40 : ((5535504682033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT166 (i+1))
      = (∑ i ∈ Finset.range 39, stT166 (i+1)) + stT166 40 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 39
    simpa using h
  have hprev := st166_p39
  have hstep := st166_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p41 : ((2426219227417/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT166 (i+1))
      = (∑ i ∈ Finset.range 40, stT166 (i+1)) + stT166 41 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 40
    simpa using h
  have hprev := st166_p40
  have hstep := st166_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p42 : ((1230413957287/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT166 (i+1))
      = (∑ i ∈ Finset.range 41, stT166 (i+1)) + stT166 42 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 41
    simpa using h
  have hprev := st166_p41
  have hstep := st166_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p43 : ((1391464195153/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT166 (i+1))
      = (∑ i ∈ Finset.range 42, stT166 (i+1)) + stT166 43 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 42
    simpa using h
  have hprev := st166_p42
  have hstep := st166_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p44 : ((3159728821391/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT166 (i+1))
      = (∑ i ∈ Finset.range 43, stT166 (i+1)) + stT166 44 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 43
    simpa using h
  have hprev := st166_p43
  have hstep := st166_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p45 : ((2845884379217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT166 (i+1))
      = (∑ i ∈ Finset.range 44, stT166 (i+1)) + stT166 45 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 44
    simpa using h
  have hprev := st166_p44
  have hstep := st166_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p46 : ((483314354873/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT166 (i+1))
      = (∑ i ∈ Finset.range 45, stT166 (i+1)) + stT166 46 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 45
    simpa using h
  have hprev := st166_p45
  have hstep := st166_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p47 : ((479476413339/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT166 (i+1))
      = (∑ i ∈ Finset.range 46, stT166 (i+1)) + stT166 47 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 46
    simpa using h
  have hprev := st166_p46
  have hstep := st166_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p48 : ((11577566013123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT166 (i+1))
      = (∑ i ∈ Finset.range 47, stT166 (i+1)) + stT166 48 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 47
    simpa using h
  have hprev := st166_p47
  have hstep := st166_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p49 : ((1543352687079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT166 (i+1))
      = (∑ i ∈ Finset.range 48, stT166 (i+1)) + stT166 49 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 48
    simpa using h
  have hprev := st166_p48
  have hstep := st166_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p50 : ((5675698637119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT166 (i+1))
      = (∑ i ∈ Finset.range 49, stT166 (i+1)) + stT166 50 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 49
    simpa using h
  have hprev := st166_p49
  have hstep := st166_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p51 : ((6235399654939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT166 (i+1))
      = (∑ i ∈ Finset.range 50, stT166 (i+1)) + stT166 51 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 50
    simpa using h
  have hprev := st166_p50
  have hstep := st166_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p52 : ((353053282389/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT166 (i+1))
      = (∑ i ∈ Finset.range 51, stT166 (i+1)) + stT166 52 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 51
    simpa using h
  have hprev := st166_p51
  have hstep := st166_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p53 : ((12474251289543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT166 (i+1))
      = (∑ i ∈ Finset.range 52, stT166 (i+1)) + stT166 53 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 52
    simpa using h
  have hprev := st166_p52
  have hstep := st166_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p54 : ((90692455167/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT166 (i+1))
      = (∑ i ∈ Finset.range 53, stT166 (i+1)) + stT166 54 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 53
    simpa using h
  have hprev := st166_p53
  have hstep := st166_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p55 : ((12387911686569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT166 (i+1))
      = (∑ i ∈ Finset.range 54, stT166 (i+1)) + stT166 55 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 54
    simpa using h
  have hprev := st166_p54
  have hstep := st166_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p56 : ((5741545767667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT166 (i+1))
      = (∑ i ∈ Finset.range 55, stT166 (i+1)) + stT166 56 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 55
    simpa using h
  have hprev := st166_p55
  have hstep := st166_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p57 : ((6082174999841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT166 (i+1))
      = (∑ i ∈ Finset.range 56, stT166 (i+1)) + stT166 57 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 56
    simpa using h
  have hprev := st166_p56
  have hstep := st166_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p58 : ((11794172027947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT166 (i+1))
      = (∑ i ∈ Finset.range 57, stT166 (i+1)) + stT166 58 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 57
    simpa using h
  have hprev := st166_p57
  have hstep := st166_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p59 : ((11770438573247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT166 (i+1))
      = (∑ i ∈ Finset.range 58, stT166 (i+1)) + stT166 59 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 58
    simpa using h
  have hprev := st166_p58
  have hstep := st166_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p60 : ((12236970239003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT166 (i+1))
      = (∑ i ∈ Finset.range 59, stT166 (i+1)) + stT166 60 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 59
    simpa using h
  have hprev := st166_p59
  have hstep := st166_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p61 : ((11347874323189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT166 (i+1))
      = (∑ i ∈ Finset.range 60, stT166 (i+1)) + stT166 61 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 60
    simpa using h
  have hprev := st166_p60
  have hstep := st166_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p62 : ((1253598692871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT166 (i+1))
      = (∑ i ∈ Finset.range 61, stT166 (i+1)) + stT166 62 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 61
    simpa using h
  have hprev := st166_p61
  have hstep := st166_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p63 : ((2821452449939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT166 (i+1))
      = (∑ i ∈ Finset.range 62, stT166 (i+1)) + stT166 63 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 62
    simpa using h
  have hprev := st166_p62
  have hstep := st166_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p64 : ((3069838387439/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT166 (i+1))
      = (∑ i ∈ Finset.range 63, stT166 (i+1)) + stT166 64 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 63
    simpa using h
  have hprev := st166_p63
  have hstep := st166_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p65 : ((2963226135621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT166 (i+1))
      = (∑ i ∈ Finset.range 64, stT166 (i+1)) + stT166 65 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 64
    simpa using h
  have hprev := st166_p64
  have hstep := st166_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p66 : ((2885210742921/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT166 (i+1))
      = (∑ i ∈ Finset.range 65, stT166 (i+1)) + stT166 66 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 65
    simpa using h
  have hprev := st166_p65
  have hstep := st166_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p67 : ((781184780699/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT166 (i+1))
      = (∑ i ∈ Finset.range 66, stT166 (i+1)) + stT166 67 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 66
    simpa using h
  have hprev := st166_p66
  have hstep := st166_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p68 : ((11286319934949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT166 (i+1))
      = (∑ i ∈ Finset.range 67, stT166 (i+1)) + stT166 68 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 67
    simpa using h
  have hprev := st166_p67
  have hstep := st166_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p69 : ((2436468362697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT166 (i+1))
      = (∑ i ∈ Finset.range 68, stT166 (i+1)) + stT166 69 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 68
    simpa using h
  have hprev := st166_p68
  have hstep := st166_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p70 : ((12079047732847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT166 (i+1))
      = (∑ i ∈ Finset.range 69, stT166 (i+1)) + stT166 70 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 69
    simpa using h
  have hprev := st166_p69
  have hstep := st166_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p71 : ((11314016012533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT166 (i+1))
      = (∑ i ∈ Finset.range 70, stT166 (i+1)) + stT166 71 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 70
    simpa using h
  have hprev := st166_p70
  have hstep := st166_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p72 : ((156137098031/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT166 (i+1))
      = (∑ i ∈ Finset.range 71, stT166 (i+1)) + stT166 72 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 71
    simpa using h
  have hprev := st166_p71
  have hstep := st166_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p73 : ((145958610073/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT166 (i+1))
      = (∑ i ∈ Finset.range 72, stT166 (i+1)) + stT166 73 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 72
    simpa using h
  have hprev := st166_p72
  have hstep := st166_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p74 : ((2886182266677/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT166 (i+1))
      = (∑ i ∈ Finset.range 73, stT166 (i+1)) + stT166 74 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 73
    simpa using h
  have hprev := st166_p73
  have hstep := st166_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p75 : ((6119554971/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT166 (i+1))
      = (∑ i ∈ Finset.range 74, stT166 (i+1)) + stT166 75 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 74
    simpa using h
  have hprev := st166_p74
  have hstep := st166_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p76 : ((2295177509617/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT166 (i+1))
      = (∑ i ∈ Finset.range 75, stT166 (i+1)) + stT166 76 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 75
    simpa using h
  have hprev := st166_p75
  have hstep := st166_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p77 : ((1170224614963/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT166 (i+1))
      = (∑ i ∈ Finset.range 76, stT166 (i+1)) + stT166 77 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 76
    simpa using h
  have hprev := st166_p76
  have hstep := st166_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p78 : ((1251413404971/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT166 (i+1))
      = (∑ i ∈ Finset.range 77, stT166 (i+1)) + stT166 78 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 77
    simpa using h
  have hprev := st166_p77
  have hstep := st166_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p79 : ((5712791078711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT166 (i+1))
      = (∑ i ∈ Finset.range 78, stT166 (i+1)) + stT166 79 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 78
    simpa using h
  have hprev := st166_p78
  have hstep := st166_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p80 : ((1464327285581/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT166 (i+1))
      = (∑ i ∈ Finset.range 79, stT166 (i+1)) + stT166 80 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 79
    simpa using h
  have hprev := st166_p79
  have hstep := st166_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p81 : ((12525363759129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT166 (i+1))
      = (∑ i ∈ Finset.range 80, stT166 (i+1)) + stT166 81 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 80
    simpa using h
  have hprev := st166_p80
  have hstep := st166_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p82 : ((2297731017793/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT166 (i+1))
      = (∑ i ∈ Finset.range 81, stT166 (i+1)) + stT166 82 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 81
    simpa using h
  have hprev := st166_p81
  have hstep := st166_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p83 : ((11586688788911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT166 (i+1))
      = (∑ i ∈ Finset.range 82, stT166 (i+1)) + stT166 83 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 82
    simpa using h
  have hprev := st166_p82
  have hstep := st166_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p84 : ((12540614808543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT166 (i+1))
      = (∑ i ∈ Finset.range 83, stT166 (i+1)) + stT166 84 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 83
    simpa using h
  have hprev := st166_p83
  have hstep := st166_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p85 : ((467624799087/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT166 (i+1))
      = (∑ i ∈ Finset.range 84, stT166 (i+1)) + stT166 85 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 84
    simpa using h
  have hprev := st166_p84
  have hstep := st166_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p86 : ((2274460588643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT166 (i+1))
      = (∑ i ∈ Finset.range 85, stT166 (i+1)) + stT166 86 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 85
    simpa using h
  have hprev := st166_p85
  have hstep := st166_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p87 : ((12443089812783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT166 (i+1))
      = (∑ i ∈ Finset.range 86, stT166 (i+1)) + stT166 87 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 86
    simpa using h
  have hprev := st166_p86
  have hstep := st166_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p88 : ((12052515541219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT166 (i+1))
      = (∑ i ∈ Finset.range 87, stT166 (i+1)) + stT166 88 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 87
    simpa using h
  have hprev := st166_p87
  have hstep := st166_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p89 : ((11228233536471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT166 (i+1))
      = (∑ i ∈ Finset.range 88, stT166 (i+1)) + stT166 89 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 88
    simpa using h
  have hprev := st166_p88
  have hstep := st166_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p90 : ((12094074192099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT166 (i+1))
      = (∑ i ∈ Finset.range 89, stT166 (i+1)) + stT166 90 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 89
    simpa using h
  have hprev := st166_p89
  have hstep := st166_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p91 : ((12446921345079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT166 (i+1))
      = (∑ i ∈ Finset.range 90, stT166 (i+1)) + stT166 91 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 90
    simpa using h
  have hprev := st166_p90
  have hstep := st166_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p92 : ((11409496570553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT166 (i+1))
      = (∑ i ∈ Finset.range 91, stT166 (i+1)) + stT166 92 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 91
    simpa using h
  have hprev := st166_p91
  have hstep := st166_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p93 : ((11537580758073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT166 (i+1))
      = (∑ i ∈ Finset.range 92, stT166 (i+1)) + stT166 93 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 92
    simpa using h
  have hprev := st166_p92
  have hstep := st166_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p94 : ((12513793917627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT166 (i+1))
      = (∑ i ∈ Finset.range 93, stT166 (i+1)) + stT166 94 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 93
    simpa using h
  have hprev := st166_p93
  have hstep := st166_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p95 : ((120089989119/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT166 (i+1))
      = (∑ i ∈ Finset.range 94, stT166 (i+1)) + stT166 95 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 94
    simpa using h
  have hprev := st166_p94
  have hstep := st166_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p96 : ((11216485684779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT166 (i+1))
      = (∑ i ∈ Finset.range 95, stT166 (i+1)) + stT166 96 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 95
    simpa using h
  have hprev := st166_p95
  have hstep := st166_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p97 : ((11966519744287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT166 (i+1))
      = (∑ i ∈ Finset.range 96, stT166 (i+1)) + stT166 97 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 96
    simpa using h
  have hprev := st166_p96
  have hstep := st166_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p98 : ((12543331688567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT166 (i+1))
      = (∑ i ∈ Finset.range 97, stT166 (i+1)) + stT166 98 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 97
    simpa using h
  have hprev := st166_p97
  have hstep := st166_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p99 : ((11658069092217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT166 (i+1))
      = (∑ i ∈ Finset.range 98, stT166 (i+1)) + stT166 99 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 98
    simpa using h
  have hprev := st166_p98
  have hstep := st166_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p100 : ((11272521092217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT166 (i+1))
      = (∑ i ∈ Finset.range 99, stT166 (i+1)) + stT166 100 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 99
    simpa using h
  have hprev := st166_p99
  have hstep := st166_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p101 : ((3054654299343/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT166 (i+1))
      = (∑ i ∈ Finset.range 100, stT166 (i+1)) + stT166 101 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 100
    simpa using h
  have hprev := st166_p100
  have hstep := st166_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p102 : ((12463622141493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT166 (i+1))
      = (∑ i ∈ Finset.range 101, stT166 (i+1)) + stT166 102 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 101
    simpa using h
  have hprev := st166_p101
  have hstep := st166_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p103 : ((11498154423633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT166 (i+1))
      = (∑ i ∈ Finset.range 102, stT166 (i+1)) + stT166 103 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 102
    simpa using h
  have hprev := st166_p102
  have hstep := st166_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p104 : ((566692756767/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT166 (i+1))
      = (∑ i ∈ Finset.range 103, stT166 (i+1)) + stT166 104 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 103
    simpa using h
  have hprev := st166_p103
  have hstep := st166_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p105 : ((614933347977/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT166 (i+1))
      = (∑ i ∈ Finset.range 104, stT166 (i+1)) + stT166 105 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 104
    simpa using h
  have hprev := st166_p104
  have hstep := st166_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p106 : ((2488347253751/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT166 (i+1))
      = (∑ i ∈ Finset.range 105, stT166 (i+1)) + stT166 106 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 105
    simpa using h
  have hprev := st166_p105
  have hstep := st166_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p107 : ((5743647598329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT166 (i+1))
      = (∑ i ∈ Finset.range 106, stT166 (i+1)) + stT166 107 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 106
    simpa using h
  have hprev := st166_p106
  have hstep := st166_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p108 : ((11308754334863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT166 (i+1))
      = (∑ i ∈ Finset.range 107, stT166 (i+1)) + stT166 108 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 107
    simpa using h
  have hprev := st166_p107
  have hstep := st166_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p109 : ((2448374067943/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT166 (i+1))
      = (∑ i ∈ Finset.range 108, stT166 (i+1)) + stT166 109 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 108
    simpa using h
  have hprev := st166_p108
  have hstep := st166_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p110 : ((12507348485147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT166 (i+1))
      = (∑ i ∈ Finset.range 109, stT166 (i+1)) + stT166 110 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 109
    simpa using h
  have hprev := st166_p109
  have hstep := st166_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p111 : ((11615925867971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT166 (i+1))
      = (∑ i ∈ Finset.range 110, stT166 (i+1)) + stT166 111 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 110
    simpa using h
  have hprev := st166_p110
  have hstep := st166_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p112 : ((11219621270963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT166 (i+1))
      = (∑ i ∈ Finset.range 111, stT166 (i+1)) + stT166 112 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 111
    simpa using h
  have hprev := st166_p111
  have hstep := st166_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p113 : ((12032202036883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT166 (i+1))
      = (∑ i ∈ Finset.range 112, stT166 (i+1)) + stT166 113 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 112
    simpa using h
  have hprev := st166_p112
  have hstep := st166_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p114 : ((12588619692703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT166 (i+1))
      = (∑ i ∈ Finset.range 113, stT166 (i+1)) + stT166 114 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 113
    simpa using h
  have hprev := st166_p113
  have hstep := st166_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p115 : ((11910863868643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT166 (i+1))
      = (∑ i ∈ Finset.range 114, stT166 (i+1)) + stT166 115 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 114
    simpa using h
  have hprev := st166_p114
  have hstep := st166_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p116 : ((5594437755529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT166 (i+1))
      = (∑ i ∈ Finset.range 115, stT166 (i+1)) + stT166 116 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 115
    simpa using h
  have hprev := st166_p115
  have hstep := st166_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p117 : ((5829747504779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT166 (i+1))
      = (∑ i ∈ Finset.range 116, stT166 (i+1)) + stT166 117 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 116
    simpa using h
  have hprev := st166_p116
  have hstep := st166_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p118 : ((6257835587981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT166 (i+1))
      = (∑ i ∈ Finset.range 117, stT166 (i+1)) + stT166 118 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 117
    simpa using h
  have hprev := st166_p117
  have hstep := st166_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p119 : ((12327968805421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT166 (i+1))
      = (∑ i ∈ Finset.range 118, stT166 (i+1)) + stT166 119 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 118
    simpa using h
  have hprev := st166_p118
  have hstep := st166_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p120 : ((11415326023171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT166 (i+1))
      = (∑ i ∈ Finset.range 119, stT166 (i+1)) + stT166 120 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 119
    simpa using h
  have hprev := st166_p119
  have hstep := st166_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p121 : ((11262655098813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT166 (i+1))
      = (∑ i ∈ Finset.range 120, stT166 (i+1)) + stT166 121 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 120
    simpa using h
  have hprev := st166_p120
  have hstep := st166_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p122 : ((12105640244369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT166 (i+1))
      = (∑ i ∈ Finset.range 121, stT166 (i+1)) + stT166 122 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 121
    simpa using h
  have hprev := st166_p121
  have hstep := st166_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p123 : ((2521286162729/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT166 (i+1))
      = (∑ i ∈ Finset.range 122, stT166 (i+1)) + stT166 123 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 122
    simpa using h
  have hprev := st166_p122
  have hstep := st166_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p124 : ((1498853826383/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT166 (i+1))
      = (∑ i ∈ Finset.range 123, stT166 (i+1)) + stT166 124 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 123
    simpa using h
  have hprev := st166_p123
  have hstep := st166_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p125 : ((560679841431/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT166 (i+1))
      = (∑ i ∈ Finset.range 124, stT166 (i+1)) + stT166 125 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 124
    simpa using h
  have hprev := st166_p124
  have hstep := st166_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p126 : ((572545873483/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT166 (i+1))
      = (∑ i ∈ Finset.range 125, stT166 (i+1)) + stT166 126 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 125
    simpa using h
  have hprev := st166_p125
  have hstep := st166_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p127 : ((3084543521447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT166 (i+1))
      = (∑ i ∈ Finset.range 126, stT166 (i+1)) + stT166 127 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 126
    simpa using h
  have hprev := st166_p126
  have hstep := st166_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p128 : ((12563372448177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT166 (i+1))
      = (∑ i ∈ Finset.range 127, stT166 (i+1)) + stT166 128 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 127
    simpa using h
  have hprev := st166_p127
  have hstep := st166_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p129 : ((11806635379089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT166 (i+1))
      = (∑ i ∈ Finset.range 128, stT166 (i+1)) + stT166 129 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 128
    simpa using h
  have hprev := st166_p128
  have hstep := st166_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p130 : ((5581005084987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT166 (i+1))
      = (∑ i ∈ Finset.range 129, stT166 (i+1)) + stT166 130 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 129
    simpa using h
  have hprev := st166_p129
  have hstep := st166_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p131 : ((5769609383207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT166 (i+1))
      = (∑ i ∈ Finset.range 130, stT166 (i+1)) + stT166 131 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 130
    simpa using h
  have hprev := st166_p130
  have hstep := st166_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p132 : ((6200642058179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT166 (i+1))
      = (∑ i ∈ Finset.range 131, stT166 (i+1)) + stT166 132 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 131
    simpa using h
  have hprev := st166_p131
  have hstep := st166_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p133 : ((6278206692447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT166 (i+1))
      = (∑ i ∈ Finset.range 132, stT166 (i+1)) + stT166 133 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 132
    simpa using h
  have hprev := st166_p132
  have hstep := st166_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p134 : ((11801285623007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT166 (i+1))
      = (∑ i ∈ Finset.range 133, stT166 (i+1)) + stT166 134 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 133
    simpa using h
  have hprev := st166_p133
  have hstep := st166_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p135 : ((11158139704323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT166 (i+1))
      = (∑ i ∈ Finset.range 134, stT166 (i+1)) + stT166 135 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 134
    simpa using h
  have hprev := st166_p134
  have hstep := st166_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p136 : ((11477137875719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT166 (i+1))
      = (∑ i ∈ Finset.range 135, stT166 (i+1)) + stT166 136 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 135
    simpa using h
  have hprev := st166_p135
  have hstep := st166_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p137 : ((1541393821231/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT166 (i+1))
      = (∑ i ∈ Finset.range 136, stT166 (i+1)) + stT166 137 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 136
    simpa using h
  have hprev := st166_p136
  have hstep := st166_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p138 : ((394142222407/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT166 (i+1))
      = (∑ i ∈ Finset.range 137, stT166 (i+1)) + stT166 138 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 137
    simpa using h
  have hprev := st166_p137
  have hstep := st166_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p139 : ((478753028367/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT166 (i+1))
      = (∑ i ∈ Finset.range 138, stT166 (i+1)) + stT166 139 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 138
    simpa using h
  have hprev := st166_p138
  have hstep := st166_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p140 : ((1121944113831/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT166 (i+1))
      = (∑ i ∈ Finset.range 139, stT166 (i+1)) + stT166 140 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 139
    simpa using h
  have hprev := st166_p139
  have hstep := st166_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p141 : ((2824081960077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT166 (i+1))
      = (∑ i ∈ Finset.range 140, stT166 (i+1)) + stT166 141 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 140
    simpa using h
  have hprev := st166_p140
  have hstep := st166_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p142 : ((6048220804017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT166 (i+1))
      = (∑ i ∈ Finset.range 141, stT166 (i+1)) + stT166 142 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 141
    simpa using h
  have hprev := st166_p141
  have hstep := st166_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p143 : ((6321391796947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT166 (i+1))
      = (∑ i ∈ Finset.range 142, stT166 (i+1)) + stT166 143 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 142
    simpa using h
  have hprev := st166_p142
  have hstep := st166_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p144 : ((3071054368427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT166 (i+1))
      = (∑ i ∈ Finset.range 143, stT166 (i+1)) + stT166 144 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 143
    simpa using h
  have hprev := st166_p143
  have hstep := st166_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p145 : ((11453936038803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT166 (i+1))
      = (∑ i ∈ Finset.range 144, stT166 (i+1)) + stT166 145 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 144
    simpa using h
  have hprev := st166_p144
  have hstep := st166_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p146 : ((11126174268987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT166 (i+1))
      = (∑ i ∈ Finset.range 145, stT166 (i+1)) + stT166 146 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 145
    simpa using h
  have hprev := st166_p145
  have hstep := st166_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p147 : ((11673668865359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT166 (i+1))
      = (∑ i ∈ Finset.range 146, stT166 (i+1)) + stT166 147 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 146
    simpa using h
  have hprev := st166_p146
  have hstep := st166_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p148 : ((12463475224307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT166 (i+1))
      = (∑ i ∈ Finset.range 147, stT166 (i+1)) + stT166 148 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 147
    simpa using h
  have hprev := st166_p147
  have hstep := st166_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p149 : ((12603925825409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT166 (i+1))
      = (∑ i ∈ Finset.range 148, stT166 (i+1)) + stT166 149 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 148
    simpa using h
  have hprev := st166_p148
  have hstep := st166_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p150 : ((5972737033607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT166 (i+1))
      = (∑ i ∈ Finset.range 149, stT166 (i+1)) + stT166 150 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 149
    simpa using h
  have hprev := st166_p149
  have hstep := st166_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p151 : ((1402495815689/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT166 (i+1))
      = (∑ i ∈ Finset.range 150, stT166 (i+1)) + stT166 151 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 150
    simpa using h
  have hprev := st166_p150
  have hstep := st166_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p152 : ((560799239817/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT166 (i+1))
      = (∑ i ∈ Finset.range 151, stT166 (i+1)) + stT166 152 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 151
    simpa using h
  have hprev := st166_p151
  have hstep := st166_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p153 : ((745647377847/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT166 (i+1))
      = (∑ i ∈ Finset.range 152, stT166 (i+1)) + stT166 153 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 152
    simpa using h
  have hprev := st166_p152
  have hstep := st166_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p154 : ((6298983936789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT166 (i+1))
      = (∑ i ∈ Finset.range 153, stT166 (i+1)) + stT166 154 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 153
    simpa using h
  have hprev := st166_p153
  have hstep := st166_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p155 : ((6259688406339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT166 (i+1))
      = (∑ i ∈ Finset.range 154, stT166 (i+1)) + stT166 155 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 154
    simpa using h
  have hprev := st166_p154
  have hstep := st166_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p156 : ((1178356531573/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT166 (i+1))
      = (∑ i ∈ Finset.range 155, stT166 (i+1)) + stT166 156 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 155
    simpa using h
  have hprev := st166_p155
  have hstep := st166_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p157 : ((11150794854997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT166 (i+1))
      = (∑ i ∈ Finset.range 156, stT166 (i+1)) + stT166 157 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 156
    simpa using h
  have hprev := st166_p156
  have hstep := st166_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p158 : ((1126063661443/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT166 (i+1))
      = (∑ i ∈ Finset.range 157, stT166 (i+1)) + stT166 158 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 157
    simpa using h
  have hprev := st166_p157
  have hstep := st166_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p159 : ((11995622799363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT166 (i+1))
      = (∑ i ∈ Finset.range 158, stT166 (i+1)) + stT166 159 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 158
    simpa using h
  have hprev := st166_p158
  have hstep := st166_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p160 : ((12622134501621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT166 (i+1))
      = (∑ i ∈ Finset.range 159, stT166 (i+1)) + stT166 160 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 159
    simpa using h
  have hprev := st166_p159
  have hstep := st166_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p161 : ((1252828545563/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT166 (i+1))
      = (∑ i ∈ Finset.range 160, stT166 (i+1)) + stT166 161 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 160
    simpa using h
  have hprev := st166_p160
  have hstep := st166_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p162 : ((2362403239891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT166 (i+1))
      = (∑ i ∈ Finset.range 161, stT166 (i+1)) + stT166 162 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 161
    simpa using h
  have hprev := st166_p161
  have hstep := st166_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p163 : ((5582306301583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT166 (i+1))
      = (∑ i ∈ Finset.range 162, stT166 (i+1)) + stT166 163 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 162
    simpa using h
  have hprev := st166_p162
  have hstep := st166_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p164 : ((5598847818861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT166 (i+1))
      = (∑ i ∈ Finset.range 163, stT166 (i+1)) + stT166 164 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 163
    simpa using h
  have hprev := st166_p163
  have hstep := st166_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p165 : ((5936770445721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT166 (i+1))
      = (∑ i ∈ Finset.range 164, stT166 (i+1)) + stT166 165 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 164
    simpa using h
  have hprev := st166_p164
  have hstep := st166_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p166 : ((6280293659571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT166 (i+1))
      = (∑ i ∈ Finset.range 165, stT166 (i+1)) + stT166 166 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 165
    simpa using h
  have hprev := st166_p165
  have hstep := st166_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p167 : ((12630109898931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT166 (i+1))
      = (∑ i ∈ Finset.range 166, stT166 (i+1)) + stT166 167 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 166
    simpa using h
  have hprev := st166_p166
  have hstep := st166_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p168 : ((12025231312727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT166 (i+1))
      = (∑ i ∈ Finset.range 167, stT166 (i+1)) + stT166 168 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 167
    simpa using h
  have hprev := st166_p167
  have hstep := st166_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p169 : ((2258781295589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT166 (i+1))
      = (∑ i ∈ Finset.range 168, stT166 (i+1)) + stT166 169 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 168
    simpa using h
  have hprev := st166_p168
  have hstep := st166_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p170 : ((554241552599/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT166 (i+1))
      = (∑ i ∈ Finset.range 169, stT166 (i+1)) + stT166 170 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 169
    simpa using h
  have hprev := st166_p169
  have hstep := st166_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p171 : ((5788005797559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT166 (i+1))
      = (∑ i ∈ Finset.range 170, stT166 (i+1)) + stT166 171 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 170
    simpa using h
  have hprev := st166_p170
  have hstep := st166_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p172 : ((6167524753179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT166 (i+1))
      = (∑ i ∈ Finset.range 171, stT166 (i+1)) + stT166 172 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 171
    simpa using h
  have hprev := st166_p171
  have hstep := st166_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p173 : ((6354335901099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT166 (i+1))
      = (∑ i ∈ Finset.range 172, stT166 (i+1)) + stT166 173 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 172
    simpa using h
  have hprev := st166_p172
  have hstep := st166_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p174 : ((12383678551393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT166 (i+1))
      = (∑ i ∈ Finset.range 173, stT166 (i+1)) + stT166 174 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 173
    simpa using h
  have hprev := st166_p173
  have hstep := st166_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p175 : ((1454932077977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT166 (i+1))
      = (∑ i ∈ Finset.range 174, stT166 (i+1)) + stT166 175 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 174
    simpa using h
  have hprev := st166_p174
  have hstep := st166_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p176 : ((5548968633771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT166 (i+1))
      = (∑ i ∈ Finset.range 175, stT166 (i+1)) + stT166 176 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 175
    simpa using h
  have hprev := st166_p175
  have hstep := st166_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p177 : ((2800526783759/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT166 (i+1))
      = (∑ i ∈ Finset.range 176, stT166 (i+1)) + stT166 177 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 176
    simpa using h
  have hprev := st166_p176
  have hstep := st166_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p178 : ((5930549643711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT166 (i+1))
      = (∑ i ∈ Finset.range 177, stT166 (i+1)) + stT166 178 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 177
    simpa using h
  have hprev := st166_p177
  have hstep := st166_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p179 : ((3134841289413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT166 (i+1))
      = (∑ i ∈ Finset.range 178, stT166 (i+1)) + stT166 179 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 178
    simpa using h
  have hprev := st166_p178
  have hstep := st166_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p180 : ((12696546365407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT166 (i+1))
      = (∑ i ∈ Finset.range 179, stT166 (i+1)) + stT166 180 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 179
    simpa using h
  have hprev := st166_p179
  have hstep := st166_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p181 : ((3053403741973/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT166 (i+1))
      = (∑ i ∈ Finset.range 180, stT166 (i+1)) + stT166 181 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 180
    simpa using h
  have hprev := st166_p180
  have hstep := st166_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p182 : ((5736644653321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT166 (i+1))
      = (∑ i ∈ Finset.range 181, stT166 (i+1)) + stT166 182 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 181
    simpa using h
  have hprev := st166_p181
  have hstep := st166_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p183 : ((1381202652431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT166 (i+1))
      = (∑ i ∈ Finset.range 182, stT166 (i+1)) + stT166 183 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 182
    simpa using h
  have hprev := st166_p182
  have hstep := st166_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p184 : ((5631740563547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT166 (i+1))
      = (∑ i ∈ Finset.range 183, stT166 (i+1)) + stT166 184 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 183
    simpa using h
  have hprev := st166_p183
  have hstep := st166_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p185 : ((5973556256427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT166 (i+1))
      = (∑ i ∈ Finset.range 184, stT166 (i+1)) + stT166 185 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 184
    simpa using h
  have hprev := st166_p184
  have hstep := st166_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p186 : ((12584049560599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT166 (i+1))
      = (∑ i ∈ Finset.range 185, stT166 (i+1)) + stT166 186 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 185
    simpa using h
  have hprev := st166_p185
  have hstep := st166_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p187 : ((12702332806599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT166 (i+1))
      = (∑ i ∈ Finset.range 186, stT166 (i+1)) + stT166 187 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 186
    simpa using h
  have hprev := st166_p186
  have hstep := st166_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p188 : ((12219849311499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT166 (i+1))
      = (∑ i ∈ Finset.range 187, stT166 (i+1)) + stT166 188 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 187
    simpa using h
  have hprev := st166_p187
  have hstep := st166_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p189 : ((5746403821159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT166 (i+1))
      = (∑ i ∈ Finset.range 188, stT166 (i+1)) + stT166 189 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 188
    simpa using h
  have hprev := st166_p188
  have hstep := st166_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p190 : ((1104673795219/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT166 (i+1))
      = (∑ i ∈ Finset.range 189, stT166 (i+1)) + stT166 190 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 189
    simpa using h
  have hprev := st166_p189
  have hstep := st166_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p191 : ((2799251907447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT166 (i+1))
      = (∑ i ∈ Finset.range 190, stT166 (i+1)) + stT166 191 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 190
    simpa using h
  have hprev := st166_p190
  have hstep := st166_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p192 : ((591606630213/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT166 (i+1))
      = (∑ i ∈ Finset.range 191, stT166 (i+1)) + stT166 192 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 191
    simpa using h
  have hprev := st166_p191
  have hstep := st166_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p193 : ((2500763146931/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT166 (i+1))
      = (∑ i ∈ Finset.range 192, stT166 (i+1)) + stT166 193 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 192
    simpa using h
  have hprev := st166_p192
  have hstep := st166_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p194 : ((12746781337351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT166 (i+1))
      = (∑ i ∈ Finset.range 193, stT166 (i+1)) + stT166 194 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 193
    simpa using h
  have hprev := st166_p193
  have hstep := st166_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p195 : ((6199143060473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT166 (i+1))
      = (∑ i ∈ Finset.range 194, stT166 (i+1)) + stT166 195 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 194
    simpa using h
  have hprev := st166_p194
  have hstep := st166_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p196 : ((2925045567569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT166 (i+1))
      = (∑ i ∈ Finset.range 195, stT166 (i+1)) + stT166 196 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 195
    simpa using h
  have hprev := st166_p195
  have hstep := st166_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p197 : ((278124825811/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT166 (i+1))
      = (∑ i ∈ Finset.range 196, stT166 (i+1)) + stT166 197 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 196
    simpa using h
  have hprev := st166_p196
  have hstep := st166_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p198 : ((552735885941/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT166 (i+1))
      = (∑ i ∈ Finset.range 197, stT166 (i+1)) + stT166 198 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 197
    simpa using h
  have hprev := st166_p197
  have hstep := st166_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p199 : ((2306249049809/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT166 (i+1))
      = (∑ i ∈ Finset.range 198, stT166 (i+1)) + stT166 199 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 198
    simpa using h
  have hprev := st166_p198
  have hstep := st166_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p200 : ((12238315186639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT166 (i+1))
      = (∑ i ∈ Finset.range 199, stT166 (i+1)) + stT166 200 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 199
    simpa using h
  have hprev := st166_p199
  have hstep := st166_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p201 : ((12716120121709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT166 (i+1))
      = (∑ i ∈ Finset.range 200, stT166 (i+1)) + stT166 201 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 200
    simpa using h
  have hprev := st166_p200
  have hstep := st166_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p202 : ((12660200967061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT166 (i+1))
      = (∑ i ∈ Finset.range 201, stT166 (i+1)) + stT166 202 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 201
    simpa using h
  have hprev := st166_p201
  have hstep := st166_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p203 : ((6055348842619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT166 (i+1))
      = (∑ i ∈ Finset.range 202, stT166 (i+1)) + stT166 203 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 202
    simpa using h
  have hprev := st166_p202
  have hstep := st166_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p204 : ((5708893870743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT166 (i+1))
      = (∑ i ∈ Finset.range 203, stT166 (i+1)) + stT166 204 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 203
    simpa using h
  have hprev := st166_p203
  have hstep := st166_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p205 : ((11014866389741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT166 (i+1))
      = (∑ i ∈ Finset.range 204, stT166 (i+1)) + stT166 205 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 204
    simpa using h
  have hprev := st166_p204
  have hstep := st166_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p206 : ((557420913069/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT166 (i+1))
      = (∑ i ∈ Finset.range 205, stT166 (i+1)) + stT166 206 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 205
    simpa using h
  have hprev := st166_p205
  have hstep := st166_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p207 : ((2933010257839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT166 (i+1))
      = (∑ i ∈ Finset.range 206, stT166 (i+1)) + stT166 207 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 206
    simpa using h
  have hprev := st166_p206
  have hstep := st166_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p208 : ((12407748142981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT166 (i+1))
      = (∑ i ∈ Finset.range 207, stT166 (i+1)) + stT166 208 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 207
    simpa using h
  have hprev := st166_p207
  have hstep := st166_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p209 : ((2553690003427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT166 (i+1))
      = (∑ i ∈ Finset.range 208, stT166 (i+1)) + stT166 209 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 208
    simpa using h
  have hprev := st166_p208
  have hstep := st166_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p210 : ((12601874295329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT166 (i+1))
      = (∑ i ∈ Finset.range 209, stT166 (i+1)) + stT166 210 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 209
    simpa using h
  have hprev := st166_p209
  have hstep := st166_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p211 : ((6005410067617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT166 (i+1))
      = (∑ i ∈ Finset.range 210, stT166 (i+1)) + stT166 211 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 210
    simpa using h
  have hprev := st166_p210
  have hstep := st166_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p212 : ((2268945810661/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT166 (i+1))
      = (∑ i ∈ Finset.range 211, stT166 (i+1)) + stT166 212 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 211
    simpa using h
  have hprev := st166_p211
  have hstep := st166_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p213 : ((2747633747181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT166 (i+1))
      = (∑ i ∈ Finset.range 212, stT166 (i+1)) + stT166 213 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 212
    simpa using h
  have hprev := st166_p212
  have hstep := st166_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p214 : ((11149220359869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT166 (i+1))
      = (∑ i ∈ Finset.range 213, stT166 (i+1)) + stT166 214 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 213
    simpa using h
  have hprev := st166_p213
  have hstep := st166_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p215 : ((11726073390871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT166 (i+1))
      = (∑ i ∈ Finset.range 214, stT166 (i+1)) + stT166 215 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 214
    simpa using h
  have hprev := st166_p214
  have hstep := st166_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p216 : ((12391824851547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT166 (i+1))
      = (∑ i ∈ Finset.range 215, stT166 (i+1)) + stT166 216 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 215
    simpa using h
  have hprev := st166_p215
  have hstep := st166_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p217 : ((12773036488187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT166 (i+1))
      = (∑ i ∈ Finset.range 216, stT166 (i+1)) + stT166 217 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 216
    simpa using h
  have hprev := st166_p216
  have hstep := st166_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p218 : ((12660495937283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT166 (i+1))
      = (∑ i ∈ Finset.range 217, stT166 (i+1)) + stT166 218 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 217
    simpa using h
  have hprev := st166_p217
  have hstep := st166_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p219 : ((12120146100011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT166 (i+1))
      = (∑ i ∈ Finset.range 218, stT166 (i+1)) + stT166 219 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 218
    simpa using h
  have hprev := st166_p218
  have hstep := st166_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p220 : ((11450142995011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT166 (i+1))
      = (∑ i ∈ Finset.range 219, stT166 (i+1)) + stT166 220 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 219
    simpa using h
  have hprev := st166_p219
  have hstep := st166_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p221 : ((11013750422299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT166 (i+1))
      = (∑ i ∈ Finset.range 220, stT166 (i+1)) + stT166 221 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 220
    simpa using h
  have hprev := st166_p220
  have hstep := st166_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p222 : ((11042941010207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT166 (i+1))
      = (∑ i ∈ Finset.range 221, stT166 (i+1)) + stT166 222 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 221
    simpa using h
  have hprev := st166_p221
  have hstep := st166_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p223 : ((11518418586167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT166 (i+1))
      = (∑ i ∈ Finset.range 222, stT166 (i+1)) + stT166 223 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 222
    simpa using h
  have hprev := st166_p222
  have hstep := st166_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p224 : ((243720888269/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT166 (i+1))
      = (∑ i ∈ Finset.range 223, stT166 (i+1)) + stT166 224 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 223
    simpa using h
  have hprev := st166_p223
  have hstep := st166_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p225 : ((793467369001/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT166 (i+1))
      = (∑ i ∈ Finset.range 224, stT166 (i+1)) + stT166 225 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 224
    simpa using h
  have hprev := st166_p224
  have hstep := st166_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p226 : ((6392046925313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT166 (i+1))
      = (∑ i ∈ Finset.range 225, stT166 (i+1)) + stT166 226 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 225
    simpa using h
  have hprev := st166_p225
  have hstep := st166_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p227 : ((1240971435491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT166 (i+1))
      = (∑ i ∈ Finset.range 226, stT166 (i+1)) + stT166 227 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 226
    simpa using h
  have hprev := st166_p226
  have hstep := st166_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p228 : ((5883347741499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT166 (i+1))
      = (∑ i ∈ Finset.range 227, stT166 (i+1)) + stT166 228 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 227
    simpa using h
  have hprev := st166_p227
  have hstep := st166_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p229 : ((447277020639/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT166 (i+1))
      = (∑ i ∈ Finset.range 228, stT166 (i+1)) + stT166 229 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 228
    simpa using h
  have hprev := st166_p228
  have hstep := st166_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p230 : ((10947822842021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT166 (i+1))
      = (∑ i ∈ Finset.range 229, stT166 (i+1)) + stT166 230 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 229
    simpa using h
  have hprev := st166_p229
  have hstep := st166_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p231 : ((5588945928973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT166 (i+1))
      = (∑ i ∈ Finset.range 230, stT166 (i+1)) + stT166 231 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 230
    simpa using h
  have hprev := st166_p230
  have hstep := st166_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p232 : ((235102584721/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT166 (i+1))
      = (∑ i ∈ Finset.range 231, stT166 (i+1)) + stT166 232 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 231
    simpa using h
  have hprev := st166_p231
  have hstep := st166_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p233 : ((3098695052189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT166 (i+1))
      = (∑ i ∈ Finset.range 232, stT166 (i+1)) + stT166 233 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 232
    simpa using h
  have hprev := st166_p232
  have hstep := st166_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p234 : ((3196594361659/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT166 (i+1))
      = (∑ i ∈ Finset.range 233, stT166 (i+1)) + stT166 234 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 233
    simpa using h
  have hprev := st166_p233
  have hstep := st166_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p235 : ((12743621846989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT166 (i+1))
      = (∑ i ∈ Finset.range 234, stT166 (i+1)) + stT166 235 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 234
    simpa using h
  have hprev := st166_p234
  have hstep := st166_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p236 : ((6145122256497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT166 (i+1))
      = (∑ i ∈ Finset.range 235, stT166 (i+1)) + stT166 236 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 235
    simpa using h
  have hprev := st166_p235
  have hstep := st166_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p237 : ((1455473650143/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT166 (i+1))
      = (∑ i ∈ Finset.range 236, stT166 (i+1)) + stT166 237 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 236
    simpa using h
  have hprev := st166_p236
  have hstep := st166_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p238 : ((1388617889583/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT166 (i+1))
      = (∑ i ∈ Finset.range 237, stT166 (i+1)) + stT166 238 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 237
    simpa using h
  have hprev := st166_p237
  have hstep := st166_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p239 : ((1366711769081/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT166 (i+1))
      = (∑ i ∈ Finset.range 238, stT166 (i+1)) + stT166 239 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 238
    simpa using h
  have hprev := st166_p238
  have hstep := st166_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p240 : ((11196169370273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT166 (i+1))
      = (∑ i ∈ Finset.range 239, stT166 (i+1)) + stT166 240 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 239
    simpa using h
  have hprev := st166_p239
  have hstep := st166_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p241 : ((11772831348749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT166 (i+1))
      = (∑ i ∈ Finset.range 240, stT166 (i+1)) + stT166 241 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 240
    simpa using h
  have hprev := st166_p240
  have hstep := st166_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p242 : ((12399331476093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT166 (i+1))
      = (∑ i ∈ Finset.range 241, stT166 (i+1)) + stT166 242 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 241
    simpa using h
  have hprev := st166_p241
  have hstep := st166_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p243 : ((12792941121593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT166 (i+1))
      = (∑ i ∈ Finset.range 242, stT166 (i+1)) + stT166 243 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 242
    simpa using h
  have hprev := st166_p242
  have hstep := st166_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p244 : ((6389706686179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT166 (i+1))
      = (∑ i ∈ Finset.range 243, stT166 (i+1)) + stT166 244 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 243
    simpa using h
  have hprev := st166_p243
  have hstep := st166_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p245 : ((494711933507/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT166 (i+1))
      = (∑ i ∈ Finset.range 244, stT166 (i+1)) + stT166 245 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 244
    simpa using h
  have hprev := st166_p244
  have hstep := st166_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p246 : ((11742224362277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT166 (i+1))
      = (∑ i ∈ Finset.range 245, stT166 (i+1)) + stT166 246 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 245
    simpa using h
  have hprev := st166_p245
  have hstep := st166_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p247 : ((11177465431697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT166 (i+1))
      = (∑ i ∈ Finset.range 246, stT166 (i+1)) + stT166 247 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 246
    simpa using h
  have hprev := st166_p246
  have hstep := st166_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p248 : ((1091777097773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT166 (i+1))
      = (∑ i ∈ Finset.range 247, stT166 (i+1)) + stT166 248 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 247
    simpa using h
  have hprev := st166_p247
  have hstep := st166_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p249 : ((5536259386921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT166 (i+1))
      = (∑ i ∈ Finset.range 248, stT166 (i+1)) + stT166 249 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 248
    simpa using h
  have hprev := st166_p248
  have hstep := st166_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_p250 : ((5786309325541/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT166 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT166 (i+1))
      = (∑ i ∈ Finset.range 249, stT166 (i+1)) + stT166 250 := by
    have h := Finset.sum_range_succ (fun i => stT166 (i+1)) 249
    simpa using h
  have hprev := st166_p249
  have hstep := st166_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st166_s250 :
    |Real.sin (((166 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))
      - ((-76513/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -329359/2000000) (δ := 169/20000000) (ψ := -123819/1000000) 166 146
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 166`** (evaluated boundary). -/
theorem station_166_sign : 0 < hardyG ((((166:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 166 250 (by norm_num) (by norm_num)
    ((-123819/1000000 : ℚ) : ℝ)
  have hchain := st166_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT166 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((166 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-123819/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st166_c250
  have hsinb := abs_le.mp st166_s250
  have hbdy_lo : ((256031824501/4409000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((166 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ))) / 2
          - ((((166:ℕ)):ℝ))
            * Real.sin (((166 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-123819/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((166:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((166:ℝ) * Real.log (250:ℝ) - ((-123819/1000000 : ℚ) : ℝ))) / 2
        - ((166:ℝ)) * Real.sin ((166:ℝ) * Real.log (250:ℝ) - ((-123819/1000000 : ℚ) : ℝ))
        ≥ ((2024111/20000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((166:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((2024111/20000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((2024111/20000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((2024111/20000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((166:ℕ)):ℝ))+1) * (((((166:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((48956600649/78125000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((5786309325541/5000000000000 : ℚ) : ℝ) + ((256031824501/4409000000000 : ℚ) : ℝ)
      - ((48956600649/78125000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-123819/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((166:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-123819/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((166:ℕ)):ℝ)))).re
      - Real.sin ((-123819/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((166:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((166:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((166:ℕ)):ℝ))
      = (((((166:ℕ)):ℝ)) * (Real.log ((((166:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((166:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_166
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
  have hθwin : |(((-123819/1000000 : ℚ) : ℝ) + ((30:ℤ)) * (2*Real.pi)) - theta ((((166:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((166:ℕ)):ℝ)))
    (φ := ((-123819/1000000 : ℚ) : ℝ) + ((30:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-123819/1000000 : ℚ)) : ℝ) 30).1,
    (cos_sin_shift (((-123819/1000000 : ℚ)) : ℝ) 30).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_166_sign
end AxiomAudit
