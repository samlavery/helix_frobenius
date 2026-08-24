import RequestProject.DVPSqrtTable

/-!
# Station `t = 60` of the extended Hardy ladder (sign +; rung-63)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT60 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((60 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))

theorem st60_c1 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((184411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 993597/10000000) (δ := 21/100000000) (ψ := -397439/1000000) 60 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t1 : ((184401/200000 : ℚ) : ℝ) ≤ stT60 1 := by
  have hc : ((184401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184401/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((184401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c2 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-412531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4990069/10000000) (δ := 457/100000000) (ψ := -397439/1000000) 60 7
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t2 : ((-729347076627/2500000000000 : ℚ) : ℝ) ≤ stT60 2 := by
  have hc : ((-412581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729347076627/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-412581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c3 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-942511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1750539/2500000) (δ := 499/100000000) (ψ := -397439/1000000) 60 11
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t3 : ((-5441878761183/10000000000000 : ℚ) : ℝ) ≤ stT60 3 := by
  have hc : ((-942561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5441878761183/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-942561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c4 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-158657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4734229/10000000) (δ := 361/100000000) (ψ := -397439/1000000) 60 13
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t4 : ((-396705079341/2500000000000 : ℚ) : ℝ) ≤ stT60 4 := by
  have hc : ((-79341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-396705079341/2500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-79341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c5 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-910767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1357967/2000000) (δ := 541/100000000) (ψ := -397439/1000000) 60 15
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t5 : ((-509162186889/1250000000000 : ℚ) : ℝ) ≤ stT60 5 := by
  have hc : ((-910817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-509162186889/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-910817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c6 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((463499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1361071/5000000) (δ := 101/25000000) (ψ := -397439/1000000) 60 17
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t6 : ((946011100209/5000000000000 : ℚ) : ℝ) ≤ stT60 6 := by
  have hc : ((463449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((946011100209/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((463449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c7 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-7641/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5571183/10000000) (δ := 169/50000000) (ψ := -397439/1000000) 60 19
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t7 : ((-46212207557/200000000000 : ℚ) : ℝ) ≤ stT60 7 := by
  have hc : ((-61133/100000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46212207557/200000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-61133/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c8 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((877691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1249437/10000000) (δ := 367/100000000) (ψ := -397439/1000000) 60 20
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t8 : ((3102928717653/10000000000000 : ℚ) : ℝ) ≤ stT60 8 := by
  have hc : ((877641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3102928717653/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((877641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c9 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((14999/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 142011/2000000) (δ := 447/100000000) (ψ := -397439/1000000) 60 21
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t9 : ((1599809840019/5000000000000 : ℚ) : ℝ) ≤ stT60 9 := by
  have hc : ((479943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1599809840019/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((479943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c10 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((118557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806169/10000000) (δ := 537/100000000) (ψ := -397439/1000000) 60 22
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t10 : ((1499561240231/5000000000000 : ℚ) : ℝ) ≤ stT60 10 := by
  have hc : ((474203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1499561240231/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((474203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c11 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((194167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -605267/10000000) (δ := 107/25000000) (ψ := -397439/1000000) 60 23
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t11 : ((585405294741/2000000000000 : ℚ) : ℝ) ≤ stT60 11 := by
  have hc : ((194157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((585405294741/2000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((194157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c12 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((131527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -815381/2500000) (δ := 81/25000000) (ψ := -397439/1000000) 60 24
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t12 : ((189806765001/2500000000000 : ℚ) : ℝ) ≤ stT60 12 := by
  have hc : ((65751/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189806765001/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((65751/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c13 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-937173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6963081/10000000) (δ := 329/100000000) (ψ := -397439/1000000) 60 25
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t13 : ((-2599388927723/10000000000000 : ℚ) : ℝ) ≤ stT60 13 := by
  have hc : ((-937223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2599388927723/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-937223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c14 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-45163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 830623/2000000) (δ := 217/50000000) (ψ := -397439/1000000) 60 25
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t14 : ((-30192509061/1250000000000 : ℚ) : ℝ) ≤ stT60 14 := by
  have hc : ((-11297/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30192509061/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-11297/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c15 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((885899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602959/5000000) (δ := 623/100000000) (ψ := -397439/1000000) 60 26
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t15 : ((571812871953/2500000000000 : ℚ) : ℝ) ≤ stT60 15 := by
  have hc : ((885849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571812871953/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((885849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c16 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-969319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7233103/10000000) (δ := 123/25000000) (ψ := -397439/1000000) 60 27
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t16 : ((-2423423469369/10000000000000 : ℚ) : ℝ) ≤ stT60 16 := by
  have hc : ((-969369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2423423469369/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-969369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c17 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((367803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186059/1000000) (δ := 93/25000000) (ψ := -397439/1000000) 60 27
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t17 : ((111499072371/625000000000 : ℚ) : ℝ) ≤ stT60 17 := by
  have hc : ((183889/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111499072371/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((183889/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c18 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-32061/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5273611/10000000) (δ := 161/50000000) (ψ := -397439/1000000) 60 28
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t18 : ((-604607040799/5000000000000 : ℚ) : ℝ) ≤ stT60 18 := by
  have hc : ((-256513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-604607040799/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-256513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c19 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((84501/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354559/1250000) (δ := 221/50000000) (ψ := -397439/1000000) 60 28
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t19 : ((193835619087/2000000000000 : ℚ) : ℝ) ≤ stT60 19 := by
  have hc : ((84491/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193835619087/2000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((84491/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c20 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-479603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5177497/10000000) (δ := 103/25000000) (ψ := -397439/1000000) 60 29
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t20 : ((-268134181101/2500000000000 : ℚ) : ℝ) ≤ stT60 20 := by
  have hc : ((-479653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268134181101/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-479653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c21 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((655153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535257/2500000) (δ := 391/100000000) (ψ := -397439/1000000) 60 29
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t21 : ((714775677167/5000000000000 : ℚ) : ℝ) ≤ stT60 21 := by
  have hc : ((655103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714775677167/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((655103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c22 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-874681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6588933/10000000) (δ := 303/100000000) (ψ := -397439/1000000) 60 30
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t22 : ((-233116686231/1250000000000 : ℚ) : ℝ) ≤ stT60 22 := by
  have hc : ((-874731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233116686231/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-874731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c23 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((999503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 78831/10000000) (δ := 27/5000000) (ψ := -397439/1000000) 60 30
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t23 : ((260500428279/1250000000000 : ℚ) : ℝ) ≤ stT60 23 := by
  have hc : ((999453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260500428279/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((999453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c24 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-424559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3231387/5000000) (δ := 21/5000000) (ψ := -397439/1000000) 60 30
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t24 : ((-54167418333/312500000000 : ℚ) : ℝ) ≤ stT60 24 := by
  have hc : ((-53073/62500 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54167418333/312500000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-53073/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c25 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((158251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3121891/10000000) (δ := 489/100000000) (ψ := -397439/1000000) 60 31
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t25 : ((79113/1250000 : ℚ) : ℝ) ≤ stT60 25 := by
  have hc : ((79113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79113/1250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((79113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c26 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((449593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21572/78125) (δ := 409/100000000) (ψ := -397439/1000000) 60 31
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t26 : ((881626199423/10000000000000 : ℚ) : ℝ) ≤ stT60 26 := by
  have hc : ((449543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((881626199423/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((449543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c27 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-38971/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3642849/5000000) (δ := 91/25000000) (ψ := -397439/1000000) 60 32
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t27 : ((-75003577473/400000000000 : ℚ) : ℝ) ≤ stT60 27 := by
  have hc : ((-38973/40000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75003577473/400000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-38973/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c28 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((185923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1830551/10000000) (δ := 559/100000000) (ψ := -397439/1000000) 60 32
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t28 : ((351337752931/2500000000000 : ℚ) : ℝ) ≤ stT60 28 := by
  have hc : ((371821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((351337752931/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((371821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c29 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((39251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3433147/10000000) (δ := 439/100000000) (ψ := -397439/1000000) 60 32
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t29 : ((72868692673/2000000000000 : ℚ) : ℝ) ≤ stT60 29 := by
  have hc : ((39241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72868692673/2000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((39241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c30 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-964893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449349/625000) (δ := 91/20000000) (ψ := -397439/1000000) 60 33
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t30 : ((-880868481353/5000000000000 : ℚ) : ℝ) ≤ stT60 30 := by
  have hc : ((-964943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-880868481353/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-964943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c31 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((614973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227111/1000000) (δ := 147/25000000) (ψ := -397439/1000000) 60 33
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t31 : ((1104434298919/10000000000000 : ℚ) : ℝ) ≤ stT60 31 := by
  have hc : ((614923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1104434298919/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((614923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c32 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((543263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 498239/2000000) (δ := 147/25000000) (ψ := -397439/1000000) 60 33
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t32 : ((480136736079/5000000000000 : ℚ) : ℝ) ≤ stT60 32 := by
  have hc : ((543213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((480136736079/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((543213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c33 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-477843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7106943/10000000) (δ := 67/20000000) (ψ := -397439/1000000) 60 33
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t33 : ((-207965405859/1250000000000 : ℚ) : ℝ) ≤ stT60 33 := by
  have hc : ((-119467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207965405859/1250000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-119467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c34 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-78353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164923/400000) (δ := 457/100000000) (ψ := -397439/1000000) 60 34
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t34 : ((-67230023679/5000000000000 : ℚ) : ℝ) ≤ stT60 34 := by
  have hc : ((-78403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67230023679/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-78403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c35 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((995951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45011/2000000) (δ := 173/50000000) (ψ := -397439/1000000) 60 34
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t35 : ((420844856877/2500000000000 : ℚ) : ℝ) ≤ stT60 35 := by
  have hc : ((995901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((420844856877/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((995901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c36 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-4159/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4450687/10000000) (δ := 377/100000000) (ψ := -397439/1000000) 60 34
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t36 : ((-21666671/625000000 : ℚ) : ℝ) ≤ stT60 36 := by
  have hc : ((-26/125 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21666671/625000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-26/125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c37 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-120041/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -714743/1000000) (δ := 263/50000000) (ψ := -397439/1000000) 60 35
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t37 : ((-78942591411/500000000000 : ℚ) : ℝ) ≤ stT60 37 := by
  have hc : ((-480189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78942591411/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-480189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c38 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((153443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3147193/10000000) (δ := 357/100000000) (ψ := -397439/1000000) 60 35
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t38 : ((62219206863/1250000000000 : ℚ) : ℝ) ≤ stT60 38 := by
  have hc : ((76709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62219206863/1250000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((76709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c39 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((955439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74913/1000000) (δ := 163/50000000) (ψ := -397439/1000000) 60 35
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t39 : ((1529846253309/10000000000000 : ℚ) : ℝ) ≤ stT60 39 := by
  have hc : ((955389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1529846253309/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((955389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c40 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-15337/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4546801/10000000) (δ := 317/100000000) (ψ := -397439/1000000) 60 35
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t40 : ((-194038959219/5000000000000 : ℚ) : ℝ) ≤ stT60 40 := by
  have hc : ((-122721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194038959219/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-122721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c41 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-246859/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7457271/10000000) (δ := 367/100000000) (ψ := -397439/1000000) 60 36
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t41 : ((-385548602667/2500000000000 : ℚ) : ℝ) ≤ stT60 41 := by
  have hc : ((-493743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385548602667/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-493743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c42 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((6747/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1921319/5000000) (δ := 129/25000000) (ψ := -397439/1000000) 60 36
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t42 : ((10395413321/2000000000000 : ℚ) : ℝ) ≤ stT60 42 := by
  have hc : ((6737/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10395413321/2000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((6737/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c43 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((99217/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313063/10000000) (δ := 129/25000000) (ψ := -397439/1000000) 60 36
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t43 : ((7564840591/50000000000 : ℚ) : ℝ) ≤ stT60 43 := by
  have hc : ((24803/25000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7564840591/50000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((24803/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c44 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((155693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 783841/2500000) (δ := 109/25000000) (ψ := -397439/1000000) 60 36
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t44 : ((14667389213/312500000000 : ℚ) : ℝ) ≤ stT60 44 := by
  have hc : ((38917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14667389213/312500000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((38917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c45 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-107273/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6506293/10000000) (δ := 527/100000000) (ψ := -397439/1000000) 60 36
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t45 : ((-79961232663/625000000000 : ℚ) : ℝ) ≤ stT60 45 := by
  have hc : ((-429117/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79961232663/625000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-429117/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c46 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-711153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2952417/5000000) (δ := 289/50000000) (ψ := -397439/1000000) 60 37
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t46 : ((-52430596363/500000000000 : ℚ) : ℝ) ≤ stT60 46 := by
  have hc : ((-711203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52430596363/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-711203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c47 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((239377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334863/1250000) (δ := 1/160000) (ψ := -397439/1000000) 60 37
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t47 : ((43641319431/625000000000 : ℚ) : ℝ) ≤ stT60 47 := by
  have hc : ((29919/62500 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43641319431/625000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((29919/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c48 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((981693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119777/2500000) (δ := 109/20000000) (ψ := -397439/1000000) 60 37
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t48 : ((11335031721/80000000000 : ℚ) : ℝ) ≤ stT60 48 := by
  have hc : ((981643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11335031721/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((981643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c49 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((141519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3572001/10000000) (δ := 289/50000000) (ψ := -397439/1000000) 60 37
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t49 : ((202098510799/10000000000000 : ℚ) : ℝ) ≤ stT60 49 := by
  have hc : ((141469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202098510799/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((141469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c50 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-5483/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6602407/10000000) (δ := 117/20000000) (ψ := -397439/1000000) 60 37
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t50 : ((-62036618431/500000000000 : ℚ) : ℝ) ≤ stT60 50 := by
  have hc : ((-87733/100000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62036618431/500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-87733/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c51 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-772817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3067581/5000000) (δ := 207/50000000) (ψ := -397439/1000000) 60 38
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t51 : ((-1082230975627/10000000000000 : ℚ) : ℝ) ≤ stT60 51 := by
  have hc : ((-772867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1082230975627/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-772867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c52 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((278101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3222449/10000000) (δ := 247/50000000) (ψ := -397439/1000000) 60 38
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t52 : ((1542348897/40000000000 : ℚ) : ℝ) ≤ stT60 52 := by
  have hc : ((278051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1542348897/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((278051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c53 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((247337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18261/500000) (δ := 267/50000000) (ψ := -397439/1000000) 60 38
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t53 : ((135890467929/1000000000000 : ℚ) : ℝ) ≤ stT60 53 := by
  have hc : ((494649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135890467929/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((494649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c54 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((140201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12193/50000) (δ := 167/50000000) (ψ := -397439/1000000) 60 38
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t54 : ((381544591779/5000000000000 : ℚ) : ℝ) ≤ stT60 54 := by
  have hc : ((280377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381544591779/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((280377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c55 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-242163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5190971/10000000) (δ := 509/100000000) (ψ := -397439/1000000) 60 38
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t55 : ((-204103937/3125000000 : ℚ) : ℝ) ≤ stT60 55 := by
  have hc : ((-60547/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204103937/3125000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-60547/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c56 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-499937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7814217/10000000) (δ := 13/2500000) (ψ := -397439/1000000) 60 39
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t56 : ((-334051360167/2500000000000 : ℚ) : ℝ) ≤ stT60 56 := by
  have hc : ((-249981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334051360167/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-249981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c57 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-118299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64491/125000) (δ := 1/250000) (ψ := -397439/1000000) 60 39
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t57 : ((-313414972059/5000000000000 : ℚ) : ℝ) ≤ stT60 57 := by
  have hc : ((-236623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313414972059/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-236623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c58 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((523189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2550519/10000000) (δ := 563/100000000) (ψ := -397439/1000000) 60 39
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t58 : ((85864373487/1250000000000 : ℚ) : ℝ) ≤ stT60 58 := by
  have hc : ((523139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85864373487/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((523139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c59 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((199997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6823/5000000) (δ := 363/100000000) (ψ := -397439/1000000) 60 39
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t59 : ((260360875443/2000000000000 : ℚ) : ℝ) ≤ stT60 59 := by
  have hc : ((199987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260360875443/2000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((199987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c60 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((264283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1267357/5000000) (δ := 9/2500000) (ψ := -397439/1000000) 60 39
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t60 : ((85288873113/1250000000000 : ℚ) : ℝ) ≤ stT60 60 := by
  have hc : ((132129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85288873113/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((132129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c61 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-52659/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5014109/10000000) (δ := 9/2500000) (ψ := -397439/1000000) 60 39
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t61 : ((-269723813909/5000000000000 : ℚ) : ℝ) ≤ stT60 61 := by
  have hc : ((-210661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269723813909/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-210661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c62 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-987177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7453187/10000000) (δ := 3/625000) (ψ := -397439/1000000) 60 39
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t62 : ((-626890132227/5000000000000 : ℚ) : ℝ) ≤ stT60 62 := by
  have hc : ((-987227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626890132227/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-987227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c63 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-17423/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234189/400000) (δ := 473/100000000) (ψ := -397439/1000000) 60 40
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t63 : ((-43904997877/500000000000 : ℚ) : ℝ) ≤ stT60 63 := by
  have hc : ((-69697/100000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43904997877/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-69697/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c64 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((86467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3492471/10000000) (δ := 49/10000000) (ψ := -397439/1000000) 60 40
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t64 : ((43221/2000000 : ℚ) : ℝ) ≤ stT60 64 := by
  have hc : ((43221/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43221/2000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((43221/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c65 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((893041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1166843/10000000) (δ := 41/10000000) (ψ := -397439/1000000) 60 40
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t65 : ((1107618707877/10000000000000 : ℚ) : ℝ) ≤ stT60 65 := by
  have hc : ((892991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1107618707877/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((892991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c66 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((450373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 561639/5000000) (δ := 353/100000000) (ψ := -397439/1000000) 60 40
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t66 : ((69292457259/625000000000 : ℚ) : ℝ) ≤ stT60 66 := by
  have hc : ((112587/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69292457259/625000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((112587/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c67 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((217461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3378959/10000000) (δ := 513/100000000) (ψ := -397439/1000000) 60 40
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t67 : ((132804857117/5000000000000 : ℚ) : ℝ) ≤ stT60 67 := by
  have hc : ((217411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132804857117/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((217411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c68 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-124149/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2800611/5000000) (δ := 593/100000000) (ψ := -397439/1000000) 60 40
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t68 : ((-150565011961/2000000000000 : ℚ) : ℝ) ≤ stT60 68 := by
  have hc : ((-124159/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150565011961/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-124159/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c69 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-999683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3895521/5000000) (δ := 593/100000000) (ψ := -397439/1000000) 60 40
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t69 : ((-1203537569647/10000000000000 : ℚ) : ℝ) ≤ stT60 69 := by
  have hc : ((-999733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1203537569647/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-999733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c70 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-668841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5758611/10000000) (δ := 191/50000000) (ψ := -397439/1000000) 60 41
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t70 : ((-799477921039/10000000000000 : ℚ) : ℝ) ≤ stT60 70 := by
  have hc : ((-668891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799477921039/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-668891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c71 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((59077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726183/2000000) (δ := 461/100000000) (ψ := -397439/1000000) 60 41
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t71 : ((17520447903/1250000000000 : ℚ) : ℝ) ≤ stT60 71 := by
  have hc : ((14763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17520447903/1250000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((14763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c72 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((163563/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1532979/10000000) (δ := 251/50000000) (ψ := -397439/1000000) 60 41
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t72 : ((192749009583/2000000000000 : ℚ) : ℝ) ≤ stT60 72 := by
  have hc : ((163553/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192749009583/2000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((163553/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c73 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((977103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 536019/10000000) (δ := 191/50000000) (ψ := -397439/1000000) 60 41
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t73 : ((1143553578783/10000000000000 : ℚ) : ℝ) ≤ stT60 73 := by
  have hc : ((977053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1143553578783/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((977053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c74 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((257089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2576867/10000000) (δ := 541/100000000) (ψ := -397439/1000000) 60 41
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t74 : ((9338460327/156250000000 : ℚ) : ℝ) ≤ stT60 74 := by
  have hc : ((32133/62500 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9338460327/156250000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((32133/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c75 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-262229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57379/125000) (δ := 271/50000000) (ψ := -397439/1000000) 60 41
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t75 : ((-302853823579/10000000000000 : ℚ) : ℝ) ≤ stT60 75 := by
  have hc : ((-262279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302853823579/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-262279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c76 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-436189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 411069/625000) (δ := 191/50000000) (ψ := -397439/1000000) 60 41
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t76 : ((-250185959453/2500000000000 : ℚ) : ℝ) ≤ stT60 76 := by
  have hc : ((-218107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250185959453/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-218107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c77 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-962811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7170047/10000000) (δ := 491/100000000) (ψ := -397439/1000000) 60 42
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t77 : ((-548641086383/5000000000000 : ℚ) : ℝ) ≤ stT60 77 := by
  have hc : ((-962861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548641086383/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-962861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c78 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-499497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -654317/1250000) (δ := 451/100000000) (ψ := -397439/1000000) 60 42
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t78 : ((-282813039033/5000000000000 : ℚ) : ℝ) ≤ stT60 78 := by
  have hc : ((-499547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282813039033/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-499547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c79 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((59747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1661841/5000000) (δ := 39/12500000) (ψ := -397439/1000000) 60 42
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t79 : ((134413018803/5000000000000 : ℚ) : ℝ) ≤ stT60 79 := by
  have hc : ((119469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134413018803/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((119469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c80 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((83933/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287373/2000000) (δ := 411/100000000) (ψ := -397439/1000000) 60 42
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t80 : ((11729284203/125000000000 : ℚ) : ℝ) ≤ stT60 80 := by
  have hc : ((10491/12500 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11729284203/125000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((10491/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c81 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((492741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 426513/10000000) (δ := 39/12500000) (ψ := -397439/1000000) 60 42
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t81 : ((136865541869/1250000000000 : ℚ) : ℝ) ≤ stT60 81 := by
  have hc : ((123179/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136865541869/1250000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((123179/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c82 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((616261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2267027/10000000) (δ := 331/100000000) (ψ := -397439/1000000) 60 42
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t82 : ((136098210093/2000000000000 : ℚ) : ℝ) ≤ stT60 82 := by
  have hc : ((616211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136098210093/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((616211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c83 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-31627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4085231/10000000) (δ := 571/100000000) (ψ := -397439/1000000) 60 42
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t83 : ((-8685649059/1250000000000 : ℚ) : ℝ) ≤ stT60 83 := by
  have hc : ((-7913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8685649059/1250000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-7913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c84 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-352303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294083/500000) (δ := 611/100000000) (ψ := -397439/1000000) 60 42
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t84 : ((-4805269469/62500000000 : ℚ) : ℝ) ≤ stT60 84 := by
  have hc : ((-44041/62500 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4805269469/62500000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-44041/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c85 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-249223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914207/2500000) (δ := 39/12500000) (ψ := -397439/1000000) 60 42
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t85 : ((-540668065563/5000000000000 : ℚ) : ℝ) ≤ stT60 85 := by
  have hc : ((-498471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-540668065563/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-498471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c86 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-812189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6296729/10000000) (δ := 281/50000000) (ψ := -397439/1000000) 60 43
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t86 : ((-109482507049/1250000000000 : ℚ) : ℝ) ≤ stT60 86 := by
  have hc : ((-812239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109482507049/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-812239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c87 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-62879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2281303/5000000) (δ := 521/100000000) (ψ := -397439/1000000) 60 43
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t87 : ((-134853589479/5000000000000 : ℚ) : ℝ) ≤ stT60 87 := by
  have hc : ((-125783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134853589479/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-125783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c88 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((104553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2848301/10000000) (δ := 521/100000000) (ψ := -397439/1000000) 60 43
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t88 : ((222880973243/5000000000000 : ℚ) : ℝ) ≤ stT60 88 := by
  have hc : ((209081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222880973243/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((209081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c89 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((447727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144171/1250000) (δ := 201/50000000) (ψ := -397439/1000000) 60 43
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t89 : ((237281388447/2500000000000 : ℚ) : ℝ) ≤ stT60 89 := by
  have hc : ((223851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237281388447/2500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((223851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c90 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((244557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522627/10000000) (δ := 201/50000000) (ψ := -397439/1000000) 60 43
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t90 : ((128886200547/1250000000000 : ℚ) : ℝ) ≤ stT60 90 := by
  have hc : ((489089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128886200547/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((489089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c91 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((128653/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1090051/5000000) (δ := 301/50000000) (ψ := -397439/1000000) 60 43
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t91 : ((33713599653/500000000000 : ℚ) : ℝ) ≤ stT60 91 := by
  have hc : ((128643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33713599653/500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((128643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c92 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((21499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3819463/10000000) (δ := 221/50000000) (ψ := -397439/1000000) 60 43
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t92 : ((2798523891/625000000000 : ℚ) : ℝ) ≤ stT60 92 := by
  have hc : ((10737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2798523891/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((10737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c93 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-569291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54411/100000) (δ := 261/50000000) (ψ := -397439/1000000) 60 43
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t93 : ((-73797411079/1250000000000 : ℚ) : ℝ) ≤ stT60 93 := by
  have hc : ((-569341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73797411079/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-569341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c94 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-948149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3522697/5000000) (δ := 241/50000000) (ψ := -397439/1000000) 60 43
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t94 : ((-488996654489/5000000000000 : ℚ) : ℝ) ≤ stT60 94 := by
  have hc : ((-948199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488996654489/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-948199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c95 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-475939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7075253/10000000) (δ := 533/100000000) (ψ := -397439/1000000) 60 44
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t95 : ((-122082267189/1250000000000 : ℚ) : ℝ) ≤ stT60 95 := by
  have hc : ((-118991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122082267189/1250000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-118991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c96 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-294987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2752279/5000000) (δ := 533/100000000) (ψ := -397439/1000000) 60 44
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t96 : ((-75273860613/1250000000000 : ℚ) : ℝ) ≤ stT60 96 := by
  have hc : ((-73753/125000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75273860613/1250000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-73753/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c97 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((-463/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197507/500000) (δ := 453/100000000) (ψ := -397439/1000000) 60 44
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t97 : ((-945288057/1000000000000 : ℚ) : ℝ) ≤ stT60 97 := by
  have hc : ((-931/100000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-945288057/1000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-931/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c98 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((569691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482333/2000000) (δ := 453/100000000) (ψ := -397439/1000000) 60 44
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t98 : ((71927999429/1250000000000 : ℚ) : ℝ) ≤ stT60 98 := by
  have hc : ((569641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71927999429/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((569641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c99 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((117183/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -888809/10000000) (δ := 31/10000000) (ψ := -397439/1000000) 60 44
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t99 : ((471067877159/5000000000000 : ℚ) : ℝ) ≤ stT60 99 := by
  have hc : ((468707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471067877159/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((468707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_c100 :
    |Real.cos (((60 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ))
      - ((969529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 618741/10000000) (δ := 493/100000000) (ψ := -397439/1000000) 60 44
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st60_t100 : ((969478030521/10000000000000 : ℚ) : ℝ) ≤ stT60 100 := by
  have hc : ((969479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((60 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-397439/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st60_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((969478030521/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((969479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st60_p1 : ((184401/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT60 (i+1) := by
  rw [Finset.sum_range_one]
  exact st60_t1

theorem st60_p2 : ((1575665423373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT60 (i+1))
      = (∑ i ∈ Finset.range 1, stT60 (i+1)) + stT60 2 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 1
    simpa using h
  have hprev := st60_p1
  have hstep := st60_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p3 : ((860782932309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT60 (i+1))
      = (∑ i ∈ Finset.range 2, stT60 (i+1)) + stT60 3 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 2
    simpa using h
  have hprev := st60_p2
  have hstep := st60_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p4 : ((-145207477011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT60 (i+1))
      = (∑ i ∈ Finset.range 3, stT60 (i+1)) + stT60 4 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 3
    simpa using h
  have hprev := st60_p3
  have hstep := st60_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p5 : ((-4799334880167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT60 (i+1))
      = (∑ i ∈ Finset.range 4, stT60 (i+1)) + stT60 5 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 4
    simpa using h
  have hprev := st60_p4
  have hstep := st60_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p6 : ((-2907312679749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT60 (i+1))
      = (∑ i ∈ Finset.range 5, stT60 (i+1)) + stT60 6 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 5
    simpa using h
  have hprev := st60_p5
  have hstep := st60_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p7 : ((-5217923057599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT60 (i+1))
      = (∑ i ∈ Finset.range 6, stT60 (i+1)) + stT60 7 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 6
    simpa using h
  have hprev := st60_p6
  have hstep := st60_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p8 : ((-1057497169973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT60 (i+1))
      = (∑ i ∈ Finset.range 7, stT60 (i+1)) + stT60 8 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 7
    simpa using h
  have hprev := st60_p7
  have hstep := st60_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p9 : ((271156335023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT60 (i+1))
      = (∑ i ∈ Finset.range 8, stT60 (i+1)) + stT60 9 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 8
    simpa using h
  have hprev := st60_p8
  have hstep := st60_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p10 : ((2041873910277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT60 (i+1))
      = (∑ i ∈ Finset.range 9, stT60 (i+1)) + stT60 10 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 9
    simpa using h
  have hprev := st60_p9
  have hstep := st60_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p11 : ((7010774294259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT60 (i+1))
      = (∑ i ∈ Finset.range 10, stT60 (i+1)) + stT60 11 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 10
    simpa using h
  have hprev := st60_p10
  have hstep := st60_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p12 : ((7770001354263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT60 (i+1))
      = (∑ i ∈ Finset.range 11, stT60 (i+1)) + stT60 12 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 11
    simpa using h
  have hprev := st60_p11
  have hstep := st60_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p13 : ((258530621327/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT60 (i+1))
      = (∑ i ∈ Finset.range 12, stT60 (i+1)) + stT60 13 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 12
    simpa using h
  have hprev := st60_p12
  have hstep := st60_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p14 : ((1232268088513/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT60 (i+1))
      = (∑ i ∈ Finset.range 13, stT60 (i+1)) + stT60 14 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 13
    simpa using h
  have hprev := st60_p13
  have hstep := st60_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p15 : ((902040480233/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT60 (i+1))
      = (∑ i ∈ Finset.range 14, stT60 (i+1)) + stT60 15 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 14
    simpa using h
  have hprev := st60_p14
  have hstep := st60_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p16 : ((958580074499/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT60 (i+1))
      = (∑ i ∈ Finset.range 15, stT60 (i+1)) + stT60 16 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 15
    simpa using h
  have hprev := st60_p15
  have hstep := st60_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p17 : ((6576885530431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT60 (i+1))
      = (∑ i ∈ Finset.range 16, stT60 (i+1)) + stT60 17 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 16
    simpa using h
  have hprev := st60_p16
  have hstep := st60_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p18 : ((5367671448833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT60 (i+1))
      = (∑ i ∈ Finset.range 17, stT60 (i+1)) + stT60 18 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 17
    simpa using h
  have hprev := st60_p17
  have hstep := st60_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p19 : ((1584212386067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT60 (i+1))
      = (∑ i ∈ Finset.range 18, stT60 (i+1)) + stT60 19 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 18
    simpa using h
  have hprev := st60_p18
  have hstep := st60_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p20 : ((658039102483/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT60 (i+1))
      = (∑ i ∈ Finset.range 19, stT60 (i+1)) + stT60 20 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 19
    simpa using h
  have hprev := st60_p19
  have hstep := st60_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p21 : ((3346932087099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT60 (i+1))
      = (∑ i ∈ Finset.range 20, stT60 (i+1)) + stT60 21 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 20
    simpa using h
  have hprev := st60_p20
  have hstep := st60_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p22 : ((96578613687/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT60 (i+1))
      = (∑ i ∈ Finset.range 21, stT60 (i+1)) + stT60 22 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 21
    simpa using h
  have hprev := st60_p21
  have hstep := st60_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p23 : ((3456467055291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT60 (i+1))
      = (∑ i ∈ Finset.range 22, stT60 (i+1)) + stT60 23 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 22
    simpa using h
  have hprev := st60_p22
  have hstep := st60_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p24 : ((2589788361963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT60 (i+1))
      = (∑ i ∈ Finset.range 23, stT60 (i+1)) + stT60 24 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 23
    simpa using h
  have hprev := st60_p23
  have hstep := st60_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p25 : ((2906240361963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT60 (i+1))
      = (∑ i ∈ Finset.range 24, stT60 (i+1)) + stT60 25 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 24
    simpa using h
  have hprev := st60_p24
  have hstep := st60_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p26 : ((6694106923349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT60 (i+1))
      = (∑ i ∈ Finset.range 25, stT60 (i+1)) + stT60 26 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 25
    simpa using h
  have hprev := st60_p25
  have hstep := st60_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p27 : ((1204754371631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT60 (i+1))
      = (∑ i ∈ Finset.range 26, stT60 (i+1)) + stT60 27 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 26
    simpa using h
  have hprev := st60_p26
  have hstep := st60_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p28 : ((778046062281/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT60 (i+1))
      = (∑ i ∈ Finset.range 27, stT60 (i+1)) + stT60 28 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 27
    simpa using h
  have hprev := st60_p27
  have hstep := st60_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p29 : ((6588711961613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT60 (i+1))
      = (∑ i ∈ Finset.range 28, stT60 (i+1)) + stT60 29 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 28
    simpa using h
  have hprev := st60_p28
  have hstep := st60_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p30 : ((4826974998907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT60 (i+1))
      = (∑ i ∈ Finset.range 29, stT60 (i+1)) + stT60 30 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 29
    simpa using h
  have hprev := st60_p29
  have hstep := st60_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p31 : ((2965704648913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT60 (i+1))
      = (∑ i ∈ Finset.range 30, stT60 (i+1)) + stT60 31 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 30
    simpa using h
  have hprev := st60_p30
  have hstep := st60_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p32 : ((107682543281/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT60 (i+1))
      = (∑ i ∈ Finset.range 31, stT60 (i+1)) + stT60 32 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 31
    simpa using h
  have hprev := st60_p31
  have hstep := st60_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p33 : ((653494940389/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT60 (i+1))
      = (∑ i ∈ Finset.range 32, stT60 (i+1)) + stT60 33 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 32
    simpa using h
  have hprev := st60_p32
  have hstep := st60_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p34 : ((2546749737877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT60 (i+1))
      = (∑ i ∈ Finset.range 33, stT60 (i+1)) + stT60 34 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 33
    simpa using h
  have hprev := st60_p33
  have hstep := st60_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p35 : ((3388439451631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT60 (i+1))
      = (∑ i ∈ Finset.range 34, stT60 (i+1)) + stT60 35 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 34
    simpa using h
  have hprev := st60_p34
  have hstep := st60_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p36 : ((3215106083631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT60 (i+1))
      = (∑ i ∈ Finset.range 35, stT60 (i+1)) + stT60 36 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 35
    simpa using h
  have hprev := st60_p35
  have hstep := st60_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p37 : ((2425680169521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT60 (i+1))
      = (∑ i ∈ Finset.range 36, stT60 (i+1)) + stT60 37 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 36
    simpa using h
  have hprev := st60_p36
  have hstep := st60_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p38 : ((2674556996973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT60 (i+1))
      = (∑ i ∈ Finset.range 37, stT60 (i+1)) + stT60 38 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 37
    simpa using h
  have hprev := st60_p37
  have hstep := st60_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p39 : ((1375792049451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT60 (i+1))
      = (∑ i ∈ Finset.range 38, stT60 (i+1)) + stT60 39 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 38
    simpa using h
  have hprev := st60_p38
  have hstep := st60_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p40 : ((6490882328817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT60 (i+1))
      = (∑ i ∈ Finset.range 39, stT60 (i+1)) + stT60 40 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 39
    simpa using h
  have hprev := st60_p39
  have hstep := st60_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p41 : ((4948687918149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT60 (i+1))
      = (∑ i ∈ Finset.range 40, stT60 (i+1)) + stT60 41 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 40
    simpa using h
  have hprev := st60_p40
  have hstep := st60_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p42 : ((2500332492377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT60 (i+1))
      = (∑ i ∈ Finset.range 41, stT60 (i+1)) + stT60 42 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 41
    simpa using h
  have hprev := st60_p41
  have hstep := st60_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p43 : ((3256816551477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT60 (i+1))
      = (∑ i ∈ Finset.range 42, stT60 (i+1)) + stT60 43 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 42
    simpa using h
  have hprev := st60_p42
  have hstep := st60_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p44 : ((698298955777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT60 (i+1))
      = (∑ i ∈ Finset.range 43, stT60 (i+1)) + stT60 44 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 43
    simpa using h
  have hprev := st60_p43
  have hstep := st60_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p45 : ((2851804917581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT60 (i+1))
      = (∑ i ∈ Finset.range 44, stT60 (i+1)) + stT60 45 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 44
    simpa using h
  have hprev := st60_p44
  have hstep := st60_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p46 : ((2327498953951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT60 (i+1))
      = (∑ i ∈ Finset.range 45, stT60 (i+1)) + stT60 46 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 45
    simpa using h
  have hprev := st60_p45
  have hstep := st60_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p47 : ((2676629509399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT60 (i+1))
      = (∑ i ∈ Finset.range 46, stT60 (i+1)) + stT60 47 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 46
    simpa using h
  have hprev := st60_p46
  have hstep := st60_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p48 : ((6770137983923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT60 (i+1))
      = (∑ i ∈ Finset.range 47, stT60 (i+1)) + stT60 48 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 47
    simpa using h
  have hprev := st60_p47
  have hstep := st60_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p49 : ((3486118247361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT60 (i+1))
      = (∑ i ∈ Finset.range 48, stT60 (i+1)) + stT60 49 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 48
    simpa using h
  have hprev := st60_p48
  have hstep := st60_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p50 : ((2865752063051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT60 (i+1))
      = (∑ i ∈ Finset.range 49, stT60 (i+1)) + stT60 50 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 49
    simpa using h
  have hprev := st60_p49
  have hstep := st60_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p51 : ((185970926019/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT60 (i+1))
      = (∑ i ∈ Finset.range 50, stT60 (i+1)) + stT60 51 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 50
    simpa using h
  have hprev := st60_p50
  have hstep := st60_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p52 : ((201394414989/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT60 (i+1))
      = (∑ i ∈ Finset.range 51, stT60 (i+1)) + stT60 52 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 51
    simpa using h
  have hprev := st60_p51
  have hstep := st60_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p53 : ((1278753010803/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT60 (i+1))
      = (∑ i ∈ Finset.range 52, stT60 (i+1)) + stT60 53 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 52
    simpa using h
  have hprev := st60_p52
  have hstep := st60_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p54 : ((7156854237573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT60 (i+1))
      = (∑ i ∈ Finset.range 53, stT60 (i+1)) + stT60 54 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 53
    simpa using h
  have hprev := st60_p53
  have hstep := st60_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p55 : ((6503721639173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT60 (i+1))
      = (∑ i ∈ Finset.range 54, stT60 (i+1)) + stT60 55 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 54
    simpa using h
  have hprev := st60_p54
  have hstep := st60_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p56 : ((1033503239701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT60 (i+1))
      = (∑ i ∈ Finset.range 55, stT60 (i+1)) + stT60 56 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 55
    simpa using h
  have hprev := st60_p55
  have hstep := st60_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p57 : ((4540686254387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT60 (i+1))
      = (∑ i ∈ Finset.range 56, stT60 (i+1)) + stT60 57 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 56
    simpa using h
  have hprev := st60_p56
  have hstep := st60_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p58 : ((5227601242283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT60 (i+1))
      = (∑ i ∈ Finset.range 57, stT60 (i+1)) + stT60 58 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 57
    simpa using h
  have hprev := st60_p57
  have hstep := st60_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p59 : ((3264702809749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT60 (i+1))
      = (∑ i ∈ Finset.range 58, stT60 (i+1)) + stT60 59 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 58
    simpa using h
  have hprev := st60_p58
  have hstep := st60_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p60 : ((3605858302201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT60 (i+1))
      = (∑ i ∈ Finset.range 59, stT60 (i+1)) + stT60 60 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 59
    simpa using h
  have hprev := st60_p59
  have hstep := st60_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p61 : ((834033622073/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT60 (i+1))
      = (∑ i ∈ Finset.range 60, stT60 (i+1)) + stT60 61 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 60
    simpa using h
  have hprev := st60_p60
  have hstep := st60_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p62 : ((541848871213/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT60 (i+1))
      = (∑ i ∈ Finset.range 61, stT60 (i+1)) + stT60 62 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 61
    simpa using h
  have hprev := st60_p61
  have hstep := st60_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p63 : ((454038875459/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT60 (i+1))
      = (∑ i ∈ Finset.range 62, stT60 (i+1)) + stT60 63 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 62
    simpa using h
  have hprev := st60_p62
  have hstep := st60_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p64 : ((475649375459/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT60 (i+1))
      = (∑ i ∈ Finset.range 63, stT60 (i+1)) + stT60 64 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 63
    simpa using h
  have hprev := st60_p63
  have hstep := st60_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p65 : ((5864112462467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT60 (i+1))
      = (∑ i ∈ Finset.range 64, stT60 (i+1)) + stT60 65 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 64
    simpa using h
  have hprev := st60_p64
  have hstep := st60_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p66 : ((6972791778611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT60 (i+1))
      = (∑ i ∈ Finset.range 65, stT60 (i+1)) + stT60 66 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 65
    simpa using h
  have hprev := st60_p65
  have hstep := st60_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p67 : ((1447680298569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT60 (i+1))
      = (∑ i ∈ Finset.range 66, stT60 (i+1)) + stT60 67 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 66
    simpa using h
  have hprev := st60_p66
  have hstep := st60_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p68 : ((81069705413/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT60 (i+1))
      = (∑ i ∈ Finset.range 67, stT60 (i+1)) + stT60 68 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 67
    simpa using h
  have hprev := st60_p67
  have hstep := st60_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p69 : ((5282038863393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT60 (i+1))
      = (∑ i ∈ Finset.range 68, stT60 (i+1)) + stT60 69 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 68
    simpa using h
  have hprev := st60_p68
  have hstep := st60_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p70 : ((2241280471177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT60 (i+1))
      = (∑ i ∈ Finset.range 69, stT60 (i+1)) + stT60 70 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 69
    simpa using h
  have hprev := st60_p69
  have hstep := st60_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p71 : ((2311362262789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT60 (i+1))
      = (∑ i ∈ Finset.range 70, stT60 (i+1)) + stT60 71 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 70
    simpa using h
  have hprev := st60_p70
  have hstep := st60_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p72 : ((5586469573493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT60 (i+1))
      = (∑ i ∈ Finset.range 71, stT60 (i+1)) + stT60 72 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 71
    simpa using h
  have hprev := st60_p71
  have hstep := st60_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p73 : ((1682505788069/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT60 (i+1))
      = (∑ i ∈ Finset.range 72, stT60 (i+1)) + stT60 73 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 72
    simpa using h
  have hprev := st60_p72
  have hstep := st60_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p74 : ((1831921153301/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT60 (i+1))
      = (∑ i ∈ Finset.range 73, stT60 (i+1)) + stT60 74 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 73
    simpa using h
  have hprev := st60_p73
  have hstep := st60_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p75 : ((56198646317/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT60 (i+1))
      = (∑ i ∈ Finset.range 74, stT60 (i+1)) + stT60 75 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 74
    simpa using h
  have hprev := st60_p74
  have hstep := st60_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p76 : ((6024086951813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT60 (i+1))
      = (∑ i ∈ Finset.range 75, stT60 (i+1)) + stT60 76 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 75
    simpa using h
  have hprev := st60_p75
  have hstep := st60_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p77 : ((4926804779047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT60 (i+1))
      = (∑ i ∈ Finset.range 76, stT60 (i+1)) + stT60 77 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 76
    simpa using h
  have hprev := st60_p76
  have hstep := st60_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p78 : ((4361178700981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT60 (i+1))
      = (∑ i ∈ Finset.range 77, stT60 (i+1)) + stT60 78 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 77
    simpa using h
  have hprev := st60_p77
  have hstep := st60_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p79 : ((4630004738587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT60 (i+1))
      = (∑ i ∈ Finset.range 78, stT60 (i+1)) + stT60 79 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 78
    simpa using h
  have hprev := st60_p78
  have hstep := st60_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p80 : ((5568347474827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT60 (i+1))
      = (∑ i ∈ Finset.range 79, stT60 (i+1)) + stT60 80 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 79
    simpa using h
  have hprev := st60_p79
  have hstep := st60_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p81 : ((6663271809779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT60 (i+1))
      = (∑ i ∈ Finset.range 80, stT60 (i+1)) + stT60 81 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 80
    simpa using h
  have hprev := st60_p80
  have hstep := st60_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p82 : ((1835940715061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT60 (i+1))
      = (∑ i ∈ Finset.range 81, stT60 (i+1)) + stT60 82 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 81
    simpa using h
  have hprev := st60_p81
  have hstep := st60_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p83 : ((1818569416943/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT60 (i+1))
      = (∑ i ∈ Finset.range 82, stT60 (i+1)) + stT60 83 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 82
    simpa using h
  have hprev := st60_p82
  have hstep := st60_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p84 : ((1626358638183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT60 (i+1))
      = (∑ i ∈ Finset.range 83, stT60 (i+1)) + stT60 84 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 83
    simpa using h
  have hprev := st60_p83
  have hstep := st60_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p85 : ((2712049210803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT60 (i+1))
      = (∑ i ∈ Finset.range 84, stT60 (i+1)) + stT60 85 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 84
    simpa using h
  have hprev := st60_p84
  have hstep := st60_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p86 : ((2274119182607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT60 (i+1))
      = (∑ i ∈ Finset.range 85, stT60 (i+1)) + stT60 86 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 85
    simpa using h
  have hprev := st60_p85
  have hstep := st60_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p87 : ((267408199141/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT60 (i+1))
      = (∑ i ∈ Finset.range 86, stT60 (i+1)) + stT60 87 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 86
    simpa using h
  have hprev := st60_p86
  have hstep := st60_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p88 : ((2362146566371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT60 (i+1))
      = (∑ i ∈ Finset.range 87, stT60 (i+1)) + stT60 88 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 87
    simpa using h
  have hprev := st60_p87
  have hstep := st60_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p89 : ((567341868653/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT60 (i+1))
      = (∑ i ∈ Finset.range 88, stT60 (i+1)) + stT60 89 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 88
    simpa using h
  have hprev := st60_p88
  have hstep := st60_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p90 : ((3352254145453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT60 (i+1))
      = (∑ i ∈ Finset.range 89, stT60 (i+1)) + stT60 90 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 89
    simpa using h
  have hprev := st60_p89
  have hstep := st60_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p91 : ((3689390141983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT60 (i+1))
      = (∑ i ∈ Finset.range 90, stT60 (i+1)) + stT60 91 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 90
    simpa using h
  have hprev := st60_p90
  have hstep := st60_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p92 : ((3711778333111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT60 (i+1))
      = (∑ i ∈ Finset.range 91, stT60 (i+1)) + stT60 92 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 91
    simpa using h
  have hprev := st60_p91
  have hstep := st60_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p93 : ((683317737759/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT60 (i+1))
      = (∑ i ∈ Finset.range 92, stT60 (i+1)) + stT60 93 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 92
    simpa using h
  have hprev := st60_p92
  have hstep := st60_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p94 : ((1463796017153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT60 (i+1))
      = (∑ i ∈ Finset.range 93, stT60 (i+1)) + stT60 94 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 93
    simpa using h
  have hprev := st60_p93
  have hstep := st60_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p95 : ((48785259311/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT60 (i+1))
      = (∑ i ∈ Finset.range 94, stT60 (i+1)) + stT60 95 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 94
    simpa using h
  have hprev := st60_p94
  have hstep := st60_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p96 : ((1069083761549/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT60 (i+1))
      = (∑ i ∈ Finset.range 95, stT60 (i+1)) + stT60 96 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 95
    simpa using h
  have hprev := st60_p95
  have hstep := st60_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p97 : ((2133441082813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT60 (i+1))
      = (∑ i ∈ Finset.range 96, stT60 (i+1)) + stT60 97 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 96
    simpa using h
  have hprev := st60_p96
  have hstep := st60_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p98 : ((2421153080529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT60 (i+1))
      = (∑ i ∈ Finset.range 97, stT60 (i+1)) + stT60 98 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 97
    simpa using h
  have hprev := st60_p97
  have hstep := st60_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p99 : ((361527619711/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT60 (i+1))
      = (∑ i ∈ Finset.range 98, stT60 (i+1)) + stT60 99 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 98
    simpa using h
  have hprev := st60_p98
  have hstep := st60_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st60_p100 : ((6753919945897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT60 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT60 (i+1))
      = (∑ i ∈ Finset.range 99, stT60 (i+1)) + stT60 100 := by
    have h := Finset.sum_range_succ (fun i => stT60 (i+1)) 99
    simpa using h
  have hprev := st60_p99
  have hstep := st60_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 60`.** -/
theorem station_60_sign : 0 < hardyG (((60:ℕ)):ℝ) := by
  have hcore := phase_station_lower 60 100 (by norm_num) (by norm_num)
    ((-397439/1000000 : ℚ) : ℝ)
  have hchain := st60_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT60 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((60:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-397439/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((60:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((60:ℕ)):ℝ)+1) * ((((60:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((643873/1200000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6753919945897/10000000000000 : ℚ) : ℝ) - ((643873/1200000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-397439/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((60:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-397439/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((60:ℕ)):ℝ))).re
      - Real.sin ((-397439/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((60:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((60:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((60:ℕ)):ℝ)
      = ((((60:ℕ)):ℝ) * (Real.log (((60:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((60:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_60
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
  have hθwin : |(((-397439/1000000 : ℚ) : ℝ) + ((6:ℤ)) * (2*Real.pi)) - theta (((60:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((60:ℕ)):ℝ))
    (φ := ((-397439/1000000 : ℚ) : ℝ) + ((6:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-397439/1000000 : ℚ)) : ℝ) 6).1,
    (cos_sin_shift (((-397439/1000000 : ℚ)) : ℝ) 6).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_60_sign
end AxiomAudit
