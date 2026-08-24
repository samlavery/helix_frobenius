import RequestProject.DVPSqrtTable

/-!
# Station `t = 11` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT11 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((11 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((330889/1000000 : ℚ) : ℝ))

theorem st11_c1 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((472877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -413611/5000000) (δ := 21/100000000) (ψ := 330889/1000000) 11 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t1 : ((118213/125000 : ℚ) : ℝ) ≤ stT11 1 := by
  have hc : ((118213/125000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118213/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((118213/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c2 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((531399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263181/5000000) (δ := 51/50000000) (ψ := 330889/1000000) 11 1
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t2 : ((3757204379383/10000000000000 : ℚ) : ℝ) ≤ stT11 2 := by
  have hc : ((531349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3757204379383/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((531349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c3 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((171917/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2031311/10000000) (δ := 103/100000000) (ψ := 330889/1000000) 11 2
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t3 : ((992490974559/2500000000000 : ℚ) : ℝ) ≤ stT11 3 := by
  have hc : ((343809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((992490974559/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((343809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c4 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-704119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2939973/5000000) (δ := 73/100000000) (ψ := 330889/1000000) 11 2
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t4 : ((-3520845704169/10000000000000 : ℚ) : ℝ) ≤ stT11 4 := by
  have hc : ((-704169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3520845704169/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-704169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c5 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((94029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -369157/1000000) (δ := 109/100000000) (ψ := 330889/1000000) 11 3
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t5 : ((84057355033/2000000000000 : ℚ) : ℝ) ≤ stT11 5 := by
  have hc : ((93979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84057355033/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((93979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c6 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((431679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1322273/10000000) (δ := 37/50000000) (ψ := 330889/1000000) 11 3
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t6 : ((440554921307/1250000000000 : ℚ) : ℝ) ≤ stT11 6 := by
  have hc : ((215827/250000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440554921307/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((215827/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c7 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-76023/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5561417/10000000) (δ := 1/1562500) (ψ := 330889/1000000) 11 3
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t7 : ((-229890859693/1000000000000 : ℚ) : ℝ) ≤ stT11 7 := by
  have hc : ((-304117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229890859693/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-304117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c8 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-212893/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6474433/10000000) (δ := 59/100000000) (ψ := 330889/1000000) 11 4
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t8 : ((-752734634037/2500000000000 : ℚ) : ℝ) ≤ stT11 8 := by
  have hc : ((-425811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-752734634037/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-425811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c9 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((273121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16177/50000) (δ := 37/50000000) (ψ := 330889/1000000) 11 4
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t9 : ((910236575643/10000000000000 : ℚ) : ℝ) ≤ stT11 9 := by
  have hc : ((273071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((910236575643/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((273071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c10 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((7927/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168993/5000000) (δ := 21/25000000) (ψ := 330889/1000000) 11 4
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t10 : ((125330524341/400000000000 : ℚ) : ℝ) ≤ stT11 10 := by
  have hc : ((39633/40000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125330524341/400000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((39633/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c11 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((305601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 570761/2500000) (δ := 1/1562500) (ψ := 330889/1000000) 11 4
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t11 : ((115168271261/625000000000 : ℚ) : ℝ) ≤ stT11 11 := by
  have hc : ((38197/62500 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115168271261/625000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((38197/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c12 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-295087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4675857/10000000) (δ := 69/100000000) (ψ := 330889/1000000) 11 4
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t12 : ((-26624603907/312500000000 : ℚ) : ℝ) ≤ stT11 12 := by
  have hc : ((-295137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26624603907/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-295137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c13 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-231153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 859629/1250000) (δ := 37/50000000) (ψ := 330889/1000000) 11 4
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t13 : ((-1282275490831/5000000000000 : ℚ) : ℝ) ≤ stT11 13 := by
  have hc : ((-462331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1282275490831/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-462331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c14 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-911283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3396481/5000000) (δ := 17/25000000) (ψ := 330889/1000000) 11 5
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t14 : ((-2435640423129/10000000000000 : ℚ) : ℝ) ≤ stT11 14 := by
  have hc : ((-911333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2435640423129/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-911333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c15 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-94461/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2447829/5000000) (δ := 49/50000000) (ψ := 330889/1000000) 11 5
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t15 : ((-487859075583/5000000000000 : ℚ) : ℝ) ≤ stT11 15 := by
  have hc : ((-188947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-487859075583/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-188947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c16 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((158449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3120849/10000000) (δ := 11/12500000) (ψ := 330889/1000000) 11 5
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t16 : ((19803/250000 : ℚ) : ℝ) ≤ stT11 16 := by
  have hc : ((19803/62500 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19803/250000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((19803/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c17 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((835657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181709/1250000) (δ := 17/25000000) (ψ := 330889/1000000) 11 5
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t17 : ((506661112773/2500000000000 : ℚ) : ℝ) ≤ stT11 17 := by
  have hc : ((835607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506661112773/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((835607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c18 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((998883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23637/2000000) (δ := 17/20000000) (ψ := 330889/1000000) 11 5
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t18 : ((1177135677663/5000000000000 : ℚ) : ℝ) ≤ stT11 18 := by
  have hc : ((998833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1177135677663/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((998833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c19 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((200223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1605033/10000000) (δ := 17/20000000) (ψ := 330889/1000000) 11 5
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t19 : ((918628640097/5000000000000 : ℚ) : ℝ) ≤ stT11 19 := by
  have hc : ((400421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((918628640097/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((400421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c20 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((71307/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3015599/10000000) (δ := 19/20000000) (ψ := 330889/1000000) 11 5
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t20 : ((159424868899/2000000000000 : ℚ) : ℝ) ≤ stT11 20 := by
  have hc : ((71297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159424868899/2000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((71297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c21 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-85643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272333/625000) (δ := 39/50000000) (ψ := 330889/1000000) 11 5
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t21 : ((-46735727643/1250000000000 : ℚ) : ℝ) ≤ stT11 21 := by
  have hc : ((-21417/125000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46735727643/1250000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-21417/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c22 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-315893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5636629/10000000) (δ := 3/4000000) (ψ := 330889/1000000) 11 5
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t22 : ((-42096231459/312500000000 : ℚ) : ℝ) ≤ stT11 22 := by
  have hc : ((-157959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42096231459/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-157959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c23 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-921849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1714763/2500000) (δ := 49/50000000) (ψ := 330889/1000000) 11 5
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t23 : ((-384458618071/2000000000000 : ℚ) : ℝ) ≤ stT11 23 := by
  have hc : ((-921899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-384458618071/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-921899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c24 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-498769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3839261/5000000) (δ := 87/100000000) (ψ := 330889/1000000) 11 6
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t24 : ((-254539815537/1250000000000 : ℚ) : ℝ) ≤ stT11 24 := by
  have hc : ((-249397/250000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254539815537/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-249397/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_c25 :
    |Real.cos (((11 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((330889/1000000 : ℚ) : ℝ))
      - ((-217051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6555917/10000000) (δ := 87/100000000) (ψ := 330889/1000000) 11 6
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st11_t25 : ((-868254434127/5000000000000 : ℚ) : ℝ) ≤ stT11 25 := by
  have hc : ((-434127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((11 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((330889/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st11_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-868254434127/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-434127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st11_p1 : ((118213/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT11 (i+1) := by
  rw [Finset.sum_range_one]
  exact st11_t1

theorem st11_p2 : ((13214244379383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT11 (i+1))
      = (∑ i ∈ Finset.range 1, stT11 (i+1)) + stT11 2 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 1
    simpa using h
  have hprev := st11_p1
  have hstep := st11_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p3 : ((17184208277619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT11 (i+1))
      = (∑ i ∈ Finset.range 2, stT11 (i+1)) + stT11 3 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 2
    simpa using h
  have hprev := st11_p2
  have hstep := st11_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p4 : ((273267251469/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT11 (i+1))
      = (∑ i ∈ Finset.range 3, stT11 (i+1)) + stT11 4 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 3
    simpa using h
  have hprev := st11_p3
  have hstep := st11_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p5 : ((2816729869723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT11 (i+1))
      = (∑ i ∈ Finset.range 4, stT11 (i+1)) + stT11 5 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 4
    simpa using h
  have hprev := st11_p4
  have hstep := st11_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p6 : ((17608088719071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT11 (i+1))
      = (∑ i ∈ Finset.range 5, stT11 (i+1)) + stT11 6 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 5
    simpa using h
  have hprev := st11_p5
  have hstep := st11_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p7 : ((15309180122141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT11 (i+1))
      = (∑ i ∈ Finset.range 6, stT11 (i+1)) + stT11 7 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 6
    simpa using h
  have hprev := st11_p6
  have hstep := st11_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p8 : ((12298241585993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT11 (i+1))
      = (∑ i ∈ Finset.range 7, stT11 (i+1)) + stT11 8 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 7
    simpa using h
  have hprev := st11_p7
  have hstep := st11_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p9 : ((3302119540409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT11 (i+1))
      = (∑ i ∈ Finset.range 8, stT11 (i+1)) + stT11 9 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 8
    simpa using h
  have hprev := st11_p8
  have hstep := st11_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p10 : ((16341741270161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT11 (i+1))
      = (∑ i ∈ Finset.range 9, stT11 (i+1)) + stT11 10 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 9
    simpa using h
  have hprev := st11_p9
  have hstep := st11_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p11 : ((18184433610337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT11 (i+1))
      = (∑ i ∈ Finset.range 10, stT11 (i+1)) + stT11 11 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 10
    simpa using h
  have hprev := st11_p10
  have hstep := st11_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p12 : ((17332446285313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT11 (i+1))
      = (∑ i ∈ Finset.range 11, stT11 (i+1)) + stT11 12 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 11
    simpa using h
  have hprev := st11_p11
  have hstep := st11_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p13 : ((14767895303651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT11 (i+1))
      = (∑ i ∈ Finset.range 12, stT11 (i+1)) + stT11 13 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 12
    simpa using h
  have hprev := st11_p12
  have hstep := st11_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p14 : ((6166127440261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT11 (i+1))
      = (∑ i ∈ Finset.range 13, stT11 (i+1)) + stT11 14 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 13
    simpa using h
  have hprev := st11_p13
  have hstep := st11_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p15 : ((2839134182339/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT11 (i+1))
      = (∑ i ∈ Finset.range 14, stT11 (i+1)) + stT11 15 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 14
    simpa using h
  have hprev := st11_p14
  have hstep := st11_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p16 : ((3037164182339/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT11 (i+1))
      = (∑ i ∈ Finset.range 15, stT11 (i+1)) + stT11 16 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 15
    simpa using h
  have hprev := st11_p15
  have hstep := st11_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p17 : ((442978161889/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT11 (i+1))
      = (∑ i ∈ Finset.range 16, stT11 (i+1)) + stT11 17 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 16
    simpa using h
  have hprev := st11_p16
  have hstep := st11_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p18 : ((8264786267887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT11 (i+1))
      = (∑ i ∈ Finset.range 17, stT11 (i+1)) + stT11 18 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 17
    simpa using h
  have hprev := st11_p17
  have hstep := st11_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p19 : ((573963431749/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT11 (i+1))
      = (∑ i ∈ Finset.range 18, stT11 (i+1)) + stT11 19 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 18
    simpa using h
  have hprev := st11_p18
  have hstep := st11_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p20 : ((19163954160463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT11 (i+1))
      = (∑ i ∈ Finset.range 19, stT11 (i+1)) + stT11 20 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 19
    simpa using h
  have hprev := st11_p19
  have hstep := st11_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p21 : ((18790068339319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT11 (i+1))
      = (∑ i ∈ Finset.range 20, stT11 (i+1)) + stT11 21 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 20
    simpa using h
  have hprev := st11_p20
  have hstep := st11_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p22 : ((17442988932631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT11 (i+1))
      = (∑ i ∈ Finset.range 21, stT11 (i+1)) + stT11 22 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 21
    simpa using h
  have hprev := st11_p21
  have hstep := st11_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p23 : ((3880173960569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT11 (i+1))
      = (∑ i ∈ Finset.range 22, stT11 (i+1)) + stT11 23 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 22
    simpa using h
  have hprev := st11_p22
  have hstep := st11_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p24 : ((674218865899/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT11 (i+1))
      = (∑ i ∈ Finset.range 23, stT11 (i+1)) + stT11 24 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 23
    simpa using h
  have hprev := st11_p23
  have hstep := st11_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st11_p25 : ((5873934224863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT11 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT11 (i+1))
      = (∑ i ∈ Finset.range 24, stT11 (i+1)) + stT11 25 := by
    have h := Finset.sum_range_succ (fun i => stT11 (i+1)) 24
    simpa using h
  have hprev := st11_p24
  have hstep := st11_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 11`.** -/
theorem station_11_sign : hardyG (((11:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 11 25 (by norm_num) (by norm_num)
    ((330889/1000000 : ℚ) : ℝ)
  have hchain := st11_p25
  have hbridge : (∑ i ∈ Finset.range 25, stT11 (i+1))
      = ∑ i ∈ Finset.range 25,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((11:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((330889/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_25
  have hsh := rpow_half_shifts (N := 25) (by norm_num)
  have hcost : ((25:ℕ):ℝ) ^ ((1/2:ℝ)) / (((11:ℕ)):ℝ)
      + ((25:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((11:ℕ)):ℝ)+1) * ((((11:ℕ)):ℝ)+2) / 8
        * (((25:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((25:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((11426005713/17187500000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((5873934224863/5000000000000 : ℚ) : ℝ) - ((11426005713/17187500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((330889/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((11:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((330889/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((11:ℕ)):ℝ))).re
      - Real.sin ((330889/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((11:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (((11:ℕ)):ℝ)) (T := (30:ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((11:ℕ)):ℝ)
      = ((((11:ℕ)):ℝ) * (Real.log (((11:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((11:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_11
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
  have hθwin : |(((330889/1000000 : ℚ) : ℝ) + ((0:ℤ)) * (2*Real.pi) - Real.pi) - theta (((11:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((11:ℕ)):ℝ))
    (φ := ((330889/1000000 : ℚ) : ℝ) + ((0:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((330889/1000000 : ℚ) : ℝ) + ((0:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((330889/1000000 : ℚ)) : ℝ) - Real.pi) + ((0:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((330889/1000000 : ℚ)) : ℝ) - Real.pi) 0).1,
    (cos_sin_shift ((((330889/1000000 : ℚ)) : ℝ) - Real.pi) 0).2]
  exact cos_sin_flip ((330889/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_11_sign
end AxiomAudit
