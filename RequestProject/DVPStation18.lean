import RequestProject.DVPSqrtTable

/-!
# Station `t = 18` of the Hardy ladder (sign +)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT18 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((18 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((80911/1000000 : ℚ) : ℝ))

theorem st18_c1 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((124591/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101139/5000000) (δ := 21/100000000) (ψ := 80911/1000000) 18 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t1 : ((498339/500000 : ℚ) : ℝ) ≤ stT18 1 := by
  have hc : ((498339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498339/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((498339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c2 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((492739/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -426581/10000000) (δ := 143/100000000) (ψ := 80911/1000000) 18 2
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t2 : ((1742006852919/2500000000000 : ℚ) : ℝ) ≤ stT18 2 := by
  have hc : ((246357/250000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1742006852919/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((246357/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c3 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((132813/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1055693/5000000) (δ := 87/50000000) (ψ := 80911/1000000) 18 3
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t3 : ((383369193053/1000000000000 : ℚ) : ℝ) ≤ stT18 3 := by
  have hc : ((132803/200000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383369193053/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((132803/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c4 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((966299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162721/2500000) (δ := 31/25000000) (ψ := 80911/1000000) 18 4
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t4 : ((966249/2000000 : ℚ) : ℝ) ≤ stT18 4 := by
  have hc : ((966249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((966249/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((966249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c5 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-816983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1579347/2500000) (δ := 21/12500000) (ψ := 80911/1000000) 18 5
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t5 : ((-456735336561/1250000000000 : ℚ) : ℝ) ≤ stT18 5 := by
  have hc : ((-817033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456735336561/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-817033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c6 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((364193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 943541/5000000) (δ := 23/20000000) (ψ := 80911/1000000) 18 5
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t6 : ((92919331561/312500000000 : ℚ) : ℝ) ≤ stT18 6 := by
  have hc : ((45521/62500 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92919331561/312500000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((45521/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c7 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-185137/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68841/100000) (δ := 53/50000000) (ψ := 80911/1000000) 18 6
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t7 : ((-139957986563/400000000000 : ℚ) : ℝ) ≤ stT18 7 := by
  have hc : ((-185147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139957986563/400000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-185147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c8 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((939347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218797/2500000) (δ := 117/100000000) (ψ := 80911/1000000) 18 6
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t8 : ((3320915540301/10000000000000 : ℚ) : ℝ) ≤ stT18 8 := by
  have hc : ((939297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3320915540301/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((939297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c9 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-49477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4425049/10000000) (δ := 73/50000000) (ψ := 80911/1000000) 18 6
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t9 : ((-164965032993/2500000000000 : ℚ) : ℝ) ≤ stT18 9 := by
  have hc : ((-98979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164965032993/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-98979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c10 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-432683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6541691/10000000) (δ := 177/100000000) (ψ := 80911/1000000) 18 7
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t10 : ((-171042873603/625000000000 : ℚ) : ℝ) ≤ stT18 10 := by
  have hc : ((-108177/125000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171042873603/625000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-108177/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c11 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((620753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2252733/10000000) (δ := 137/100000000) (ψ := 80911/1000000) 18 7
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t11 : ((1871489684439/10000000000000 : ℚ) : ℝ) ≤ stT18 11 := by
  have hc : ((620703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1871489684439/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((620703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c12 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((24589/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1662779/10000000) (δ := 97/100000000) (ψ := 80911/1000000) 18 7
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t12 : ((1135644956649/5000000000000 : ℚ) : ℝ) ≤ stT18 12 := by
  have hc : ((393399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1135644956649/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((393399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c13 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-509913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5264701/10000000) (δ := 117/100000000) (ψ := 80911/1000000) 18 7
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t13 : ((-1414382890463/10000000000000 : ℚ) : ℝ) ≤ stT18 13 := by
  have hc : ((-509963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1414382890463/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-509963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c14 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-477929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1777101/2500000) (δ := 17/12500000) (ψ := 80911/1000000) 18 8
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t14 : ((-638693036901/2500000000000 : ℚ) : ℝ) ≤ stT18 14 := by
  have hc : ((-238977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638693036901/2500000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-238977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c15 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-30689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -160149/400000) (δ := 49/25000000) (ψ := 80911/1000000) 18 8
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t15 : ((-79367759871/10000000000000 : ℚ) : ℝ) ≤ stT18 15 := by
  have hc : ((-30739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79367759871/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-30739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c16 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((452419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1099491/10000000) (δ := 17/12500000) (ψ := 80911/1000000) 18 8
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t16 : ((226197/1000000 : ℚ) : ℝ) ≤ stT18 16 := by
  have hc : ((226197/250000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226197/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((226197/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c17 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((795207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1628617/10000000) (δ := 3/3125000) (ψ := 80911/1000000) 18 8
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t17 : ((482134700223/2500000000000 : ℚ) : ℝ) ≤ stT18 17 := by
  have hc : ((795157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482134700223/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((795157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c18 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-109283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 840149/2000000) (δ := 3/3125000) (ψ := 80911/1000000) 18 8
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t18 : ((-257700395659/10000000000000 : ℚ) : ℝ) ≤ stT18 18 := by
  have hc : ((-109333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-257700395659/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-109333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c19 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-883233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 663377/1000000) (δ := 127/100000000) (ψ := 80911/1000000) 18 8
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t19 : ((-1013195380357/5000000000000 : ℚ) : ℝ) ≤ stT18 19 := by
  have hc : ((-883283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1013195380357/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-883283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c20 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-226697/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353199/2000000) (δ := 59/50000000) (ψ := 80911/1000000) 18 9
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t20 : ((-253468929123/1250000000000 : ℚ) : ℝ) ≤ stT18 20 := by
  have hc : ((-453419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253468929123/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-453419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c21 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-127273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4570437/10000000) (δ := 21/20000000) (ψ := 80911/1000000) 18 9
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t21 : ((-138893511171/2500000000000 : ℚ) : ℝ) ≤ stT18 21 := by
  have hc : ((-63649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138893511171/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-63649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c22 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((68501/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2477037/10000000) (δ := 21/20000000) (ψ := 80911/1000000) 18 9
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t22 : ((584125145853/5000000000000 : ℚ) : ℝ) ≤ stT18 22 := by
  have hc : ((273979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584125145853/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((273979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c23 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((1571/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -476707/10000000) (δ := 29/20000000) (ψ := 80911/1000000) 18 9
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t23 : ((10236232539/50000000000 : ℚ) : ℝ) ≤ stT18 23 := by
  have hc : ((39273/40000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10236232539/50000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((39273/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c24 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((41949/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57539/400000) (δ := 29/20000000) (ψ := 80911/1000000) 18 9
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t24 : ((171245831213/1000000000000 : ℚ) : ℝ) ≤ stT18 24 := by
  have hc : ((83893/100000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171245831213/1000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((83893/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c25 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((25767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655093/2000000) (δ := 29/20000000) (ψ := 80911/1000000) 18 9
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t25 : ((12881/250000 : ℚ) : ℝ) ≤ stT18 25 := by
  have hc : ((12881/50000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12881/250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((12881/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c26 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-86157/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5040397/10000000) (δ := 1/800000) (ψ := 80911/1000000) 18 9
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t26 : ((-84493723027/1000000000000 : ℚ) : ℝ) ≤ stT18 26 := by
  have hc : ((-86167/200000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84493723027/1000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-86167/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c27 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-902133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842339/1250000) (δ := 59/50000000) (ψ := 80911/1000000) 18 9
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t27 : ((-1736252085683/10000000000000 : ℚ) : ℝ) ≤ stT18 27 := by
  have hc : ((-902183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1736252085683/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-902183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c28 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-48917/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7332707/10000000) (δ := 77/50000000) (ψ := 80911/1000000) 18 10
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t28 : ((-184898392497/1000000000000 : ℚ) : ℝ) ≤ stT18 28 := by
  have hc : ((-97839/100000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184898392497/1000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-97839/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c29 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-667349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2876799/5000000) (δ := 67/50000000) (ψ := 80911/1000000) 18 10
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t29 : ((-619664621323/5000000000000 : ℚ) : ℝ) ≤ stT18 29 := by
  have hc : ((-667399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619664621323/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-667399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c30 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-30031/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1057007/2500000) (δ := 149/100000000) (ψ := 80911/1000000) 18 10
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t30 : ((-54851679777/2500000000000 : ℚ) : ℝ) ≤ stT18 30 := by
  have hc : ((-60087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54851679777/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-60087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c31 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((45271/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1376243/5000000) (δ := 87/50000000) (ψ := 80911/1000000) 18 10
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t31 : ((40650067549/500000000000 : ℚ) : ℝ) ≤ stT18 31 := by
  have hc : ((22633/50000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40650067549/500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((22633/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c32 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((863051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264759/2000000) (δ := 97/50000000) (ψ := 80911/1000000) 18 10
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t32 : ((762791912883/5000000000000 : ℚ) : ℝ) ≤ stT18 32 := by
  have hc : ((863001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((762791912883/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((863001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c33 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((999703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6093/1000000) (δ := 109/100000000) (ψ := 80911/1000000) 18 10
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t33 : ((217521493841/1250000000000 : ℚ) : ℝ) ≤ stT18 33 := by
  have hc : ((999653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217521493841/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((999653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c34 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((846337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1404313/10000000) (δ := 77/50000000) (ψ := 80911/1000000) 18 10
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t34 : ((290273902139/2000000000000 : ℚ) : ℝ) ≤ stT18 34 := by
  have hc : ((846287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290273902139/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((846287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c35 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((234119/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2708753/10000000) (δ := 129/100000000) (ψ := 80911/1000000) 18 10
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t35 : ((49461370119/625000000000 : ℚ) : ℝ) ≤ stT18 35 := by
  have hc : ((117047/250000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49461370119/625000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((117047/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c36 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-19779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1988221/5000000) (δ := 57/50000000) (ψ := 80911/1000000) 18 10
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t36 : ((-33048339943/10000000000000 : ℚ) : ℝ) ≤ stT18 36 := by
  have hc : ((-19829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33048339943/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-19829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c37 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-12269/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1302349/2500000) (δ := 77/50000000) (ψ := 80911/1000000) 18 10
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t37 : ((-8068867319/100000000000 : ℚ) : ℝ) ≤ stT18 37 := by
  have hc : ((-49081/100000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8068867319/100000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-49081/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c38 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-837663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6409467/10000000) (δ := 109/100000000) (ψ := 80911/1000000) 18 10
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t38 : ((-271790118859/2000000000000 : ℚ) : ℝ) ≤ stT18 38 := by
  have hc : ((-837713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271790118859/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-837713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c39 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-993929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1894591/2500000) (δ := 47/50000000) (ψ := 80911/1000000) 18 10
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t39 : ((-795820340539/5000000000000 : ℚ) : ℝ) ≤ stT18 39 := by
  have hc : ((-993979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-795820340539/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-993979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c40 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-188183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3495149/5000000) (δ := 99/100000000) (ψ := 80911/1000000) 18 11
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t40 : ((-297559291827/2000000000000 : ℚ) : ℝ) ≤ stT18 40 := by
  have hc : ((-188193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297559291827/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-188193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c41 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-703887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -587913/1000000) (δ := 139/100000000) (ψ := 80911/1000000) 18 11
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t41 : ((-549682581253/5000000000000 : ℚ) : ℝ) ≤ stT18 41 := by
  have hc : ((-703937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-549682581253/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-703937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c42 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((-85043/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4794741/10000000) (δ := 41/25000000) (ψ := 80911/1000000) 18 11
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t42 : ((-131243528387/2500000000000 : ℚ) : ℝ) ≤ stT18 42 := by
  have hc : ((-170111/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131243528387/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-170111/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c43 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((611/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -933967/2500000) (δ := 9/6250000) (ψ := 80911/1000000) 18 11
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t43 : ((931155841/80000000000 : ℚ) : ℝ) ≤ stT18 43 := by
  have hc : ((3053/40000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((931155841/80000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((3053/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c44 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((58857/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -135067/500000) (δ := 31/25000000) (ψ := 80911/1000000) 18 11
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t44 : ((88720801267/1250000000000 : ℚ) : ℝ) ≤ stT18 44 := by
  have hc : ((235403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88720801267/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((235403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c45 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((390033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1690061/10000000) (δ := 179/100000000) (ψ := 80911/1000000) 18 11
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t45 : ((72673651961/625000000000 : ℚ) : ℝ) ≤ stT18 45 := by
  have hc : ((48751/62500 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72673651961/625000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((48751/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c46 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((60059/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701011/10000000) (δ := 159/100000000) (ψ := 80911/1000000) 18 11
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t46 : ((708380185293/5000000000000 : ℚ) : ℝ) ≤ stT18 46 := by
  have hc : ((480447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((708380185293/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((480447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_c47 :
    |Real.cos (((18 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((80911/1000000 : ℚ) : ℝ))
      - ((124289/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266769/10000000) (δ := 41/25000000) (ψ := 80911/1000000) 18 11
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st18_t47 : ((725139636019/5000000000000 : ℚ) : ℝ) ≤ stT18 47 := by
  have hc : ((497131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((18 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((80911/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st18_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((725139636019/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((497131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st18_p1 : ((498339/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT18 (i+1) := by
  rw [Finset.sum_range_one]
  exact st18_t1

theorem st18_p2 : ((4233701852919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT18 (i+1))
      = (∑ i ∈ Finset.range 1, stT18 (i+1)) + stT18 2 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 1
    simpa using h
  have hprev := st18_p1
  have hstep := st18_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p3 : ((10384249671103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT18 (i+1))
      = (∑ i ∈ Finset.range 2, stT18 (i+1)) + stT18 3 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 2
    simpa using h
  have hprev := st18_p2
  have hstep := st18_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p4 : ((12799872171103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT18 (i+1))
      = (∑ i ∈ Finset.range 3, stT18 (i+1)) + stT18 4 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 3
    simpa using h
  have hprev := st18_p3
  have hstep := st18_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p5 : ((10972930824859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT18 (i+1))
      = (∑ i ∈ Finset.range 4, stT18 (i+1)) + stT18 5 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 4
    simpa using h
  have hprev := st18_p4
  have hstep := st18_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p6 : ((2491928025967/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT18 (i+1))
      = (∑ i ∈ Finset.range 5, stT18 (i+1)) + stT18 6 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 5
    simpa using h
  have hprev := st18_p5
  have hstep := st18_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p7 : ((4284066119119/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT18 (i+1))
      = (∑ i ∈ Finset.range 6, stT18 (i+1)) + stT18 7 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 6
    simpa using h
  have hprev := st18_p6
  have hstep := st18_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p8 : ((3092655766987/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT18 (i+1))
      = (∑ i ∈ Finset.range 7, stT18 (i+1)) + stT18 8 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 7
    simpa using h
  have hprev := st18_p7
  have hstep := st18_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p9 : ((6020346500981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT18 (i+1))
      = (∑ i ∈ Finset.range 8, stT18 (i+1)) + stT18 9 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 8
    simpa using h
  have hprev := st18_p8
  have hstep := st18_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p10 : ((5336175006569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT18 (i+1))
      = (∑ i ∈ Finset.range 9, stT18 (i+1)) + stT18 10 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 9
    simpa using h
  have hprev := st18_p9
  have hstep := st18_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p11 : ((4643237942143/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT18 (i+1))
      = (∑ i ∈ Finset.range 10, stT18 (i+1)) + stT18 11 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 10
    simpa using h
  have hprev := st18_p10
  have hstep := st18_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p12 : ((25487479624013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT18 (i+1))
      = (∑ i ∈ Finset.range 11, stT18 (i+1)) + stT18 12 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 11
    simpa using h
  have hprev := st18_p11
  have hstep := st18_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p13 : ((481461934671/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT18 (i+1))
      = (∑ i ∈ Finset.range 12, stT18 (i+1)) + stT18 13 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 12
    simpa using h
  have hprev := st18_p12
  have hstep := st18_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p14 : ((10759162292973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT18 (i+1))
      = (∑ i ∈ Finset.range 13, stT18 (i+1)) + stT18 14 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 13
    simpa using h
  have hprev := st18_p13
  have hstep := st18_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p15 : ((857558273043/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT18 (i+1))
      = (∑ i ∈ Finset.range 14, stT18 (i+1)) + stT18 15 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 14
    simpa using h
  have hprev := st18_p14
  have hstep := st18_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p16 : ((948037073043/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT18 (i+1))
      = (∑ i ∈ Finset.range 15, stT18 (i+1)) + stT18 16 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 15
    simpa using h
  have hprev := st18_p15
  have hstep := st18_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p17 : ((25629465626967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT18 (i+1))
      = (∑ i ∈ Finset.range 16, stT18 (i+1)) + stT18 17 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 16
    simpa using h
  have hprev := st18_p16
  have hstep := st18_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p18 : ((6342941307827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT18 (i+1))
      = (∑ i ∈ Finset.range 17, stT18 (i+1)) + stT18 18 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 17
    simpa using h
  have hprev := st18_p17
  have hstep := st18_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p19 : ((11672687235297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT18 (i+1))
      = (∑ i ∈ Finset.range 18, stT18 (i+1)) + stT18 19 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 18
    simpa using h
  have hprev := st18_p18
  have hstep := st18_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p20 : ((2131762303761/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT18 (i+1))
      = (∑ i ∈ Finset.range 19, stT18 (i+1)) + stT18 20 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 19
    simpa using h
  have hprev := st18_p19
  have hstep := st18_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p21 : ((10381024496463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT18 (i+1))
      = (∑ i ∈ Finset.range 20, stT18 (i+1)) + stT18 21 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 20
    simpa using h
  have hprev := st18_p20
  have hstep := st18_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p22 : ((2741287410579/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT18 (i+1))
      = (∑ i ∈ Finset.range 21, stT18 (i+1)) + stT18 22 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 21
    simpa using h
  have hprev := st18_p21
  have hstep := st18_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p23 : ((1498596612027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT18 (i+1))
      = (∑ i ∈ Finset.range 22, stT18 (i+1)) + stT18 23 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 22
    simpa using h
  have hprev := st18_p22
  have hstep := st18_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p24 : ((12845002052281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT18 (i+1))
      = (∑ i ∈ Finset.range 23, stT18 (i+1)) + stT18 24 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 23
    simpa using h
  have hprev := st18_p23
  have hstep := st18_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p25 : ((13102622052281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT18 (i+1))
      = (∑ i ∈ Finset.range 24, stT18 (i+1)) + stT18 25 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 24
    simpa using h
  have hprev := st18_p24
  have hstep := st18_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p26 : ((6340076718573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT18 (i+1))
      = (∑ i ∈ Finset.range 25, stT18 (i+1)) + stT18 26 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 25
    simpa using h
  have hprev := st18_p25
  have hstep := st18_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p27 : ((23624054788609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT18 (i+1))
      = (∑ i ∈ Finset.range 26, stT18 (i+1)) + stT18 27 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 26
    simpa using h
  have hprev := st18_p26
  have hstep := st18_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p28 : ((21775070863639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT18 (i+1))
      = (∑ i ∈ Finset.range 27, stT18 (i+1)) + stT18 28 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 27
    simpa using h
  have hprev := st18_p27
  have hstep := st18_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p29 : ((20535741620993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT18 (i+1))
      = (∑ i ∈ Finset.range 28, stT18 (i+1)) + stT18 29 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 28
    simpa using h
  have hprev := st18_p28
  have hstep := st18_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p30 : ((4063266980377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT18 (i+1))
      = (∑ i ∈ Finset.range 29, stT18 (i+1)) + stT18 30 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 29
    simpa using h
  have hprev := st18_p29
  have hstep := st18_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p31 : ((4225867250573/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT18 (i+1))
      = (∑ i ∈ Finset.range 30, stT18 (i+1)) + stT18 31 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 30
    simpa using h
  have hprev := st18_p30
  have hstep := st18_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p32 : ((22654920078631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT18 (i+1))
      = (∑ i ∈ Finset.range 31, stT18 (i+1)) + stT18 32 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 31
    simpa using h
  have hprev := st18_p31
  have hstep := st18_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p33 : ((24395092029359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT18 (i+1))
      = (∑ i ∈ Finset.range 32, stT18 (i+1)) + stT18 33 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 32
    simpa using h
  have hprev := st18_p32
  have hstep := st18_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p34 : ((12923230770027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT18 (i+1))
      = (∑ i ∈ Finset.range 33, stT18 (i+1)) + stT18 34 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 33
    simpa using h
  have hprev := st18_p33
  have hstep := st18_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p35 : ((13318921730979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT18 (i+1))
      = (∑ i ∈ Finset.range 34, stT18 (i+1)) + stT18 35 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 34
    simpa using h
  have hprev := st18_p34
  have hstep := st18_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p36 : ((5320959024403/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT18 (i+1))
      = (∑ i ∈ Finset.range 35, stT18 (i+1)) + stT18 36 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 35
    simpa using h
  have hprev := st18_p35
  have hstep := st18_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p37 : ((5159581678023/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT18 (i+1))
      = (∑ i ∈ Finset.range 36, stT18 (i+1)) + stT18 37 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 36
    simpa using h
  have hprev := st18_p36
  have hstep := st18_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p38 : ((1221947889791/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT18 (i+1))
      = (∑ i ∈ Finset.range 37, stT18 (i+1)) + stT18 38 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 37
    simpa using h
  have hprev := st18_p37
  have hstep := st18_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p39 : ((11423658557371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT18 (i+1))
      = (∑ i ∈ Finset.range 38, stT18 (i+1)) + stT18 39 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 38
    simpa using h
  have hprev := st18_p38
  have hstep := st18_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p40 : ((21359520655607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT18 (i+1))
      = (∑ i ∈ Finset.range 39, stT18 (i+1)) + stT18 40 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 39
    simpa using h
  have hprev := st18_p39
  have hstep := st18_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p41 : ((20260155493101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT18 (i+1))
      = (∑ i ∈ Finset.range 40, stT18 (i+1)) + stT18 41 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 40
    simpa using h
  have hprev := st18_p40
  have hstep := st18_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p42 : ((19735181379553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT18 (i+1))
      = (∑ i ∈ Finset.range 41, stT18 (i+1)) + stT18 42 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 41
    simpa using h
  have hprev := st18_p41
  have hstep := st18_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p43 : ((9925787929839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT18 (i+1))
      = (∑ i ∈ Finset.range 42, stT18 (i+1)) + stT18 43 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 42
    simpa using h
  have hprev := st18_p42
  have hstep := st18_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p44 : ((10280671134907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT18 (i+1))
      = (∑ i ∈ Finset.range 43, stT18 (i+1)) + stT18 44 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 43
    simpa using h
  have hprev := st18_p43
  have hstep := st18_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p45 : ((2172412070119/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT18 (i+1))
      = (∑ i ∈ Finset.range 44, stT18 (i+1)) + stT18 45 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 44
    simpa using h
  have hprev := st18_p44
  have hstep := st18_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p46 : ((723152533493/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT18 (i+1))
      = (∑ i ∈ Finset.range 45, stT18 (i+1)) + stT18 46 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 45
    simpa using h
  have hprev := st18_p45
  have hstep := st18_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st18_p47 : ((12295580171907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT18 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT18 (i+1))
      = (∑ i ∈ Finset.range 46, stT18 (i+1)) + stT18 47 := by
    have h := Finset.sum_range_succ (fun i => stT18 (i+1)) 46
    simpa using h
  have hprev := st18_p46
  have hstep := st18_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 18`.** -/
theorem station_18_sign : 0 < hardyG (((18:ℕ)):ℝ) := by
  have hcore := phase_station_lower 18 47 (by norm_num) (by norm_num)
    ((80911/1000000 : ℚ) : ℝ)
  have hchain := st18_p47
  have hbridge : (∑ i ∈ Finset.range 47, stT18 (i+1))
      = ∑ i ∈ Finset.range 47,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((18:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((80911/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_47
  have hsh := rpow_half_shifts (N := 47) (by norm_num)
  have hcost : ((47:ℕ):ℝ) ^ ((1/2:ℝ)) / (((18:ℕ)):ℝ)
      + ((47:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((18:ℕ)):ℝ)+1) * ((((18:ℕ)):ℝ)+2) / 8
        * (((47:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((47:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((4415304377/7952400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12295580171907/5000000000000 : ℚ) : ℝ) - ((4415304377/7952400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((80911/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((18:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((80911/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((18:ℕ)):ℝ))).re
      - Real.sin ((80911/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((18:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (((18:ℕ)):ℝ)) (T := (30:ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((18:ℕ)):ℝ)
      = ((((18:ℕ)):ℝ) * (Real.log (((18:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((18:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_18
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
  have hθwin : |(((80911/1000000 : ℚ) : ℝ) + ((0:ℤ)) * (2*Real.pi)) - theta (((18:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((18:ℕ)):ℝ))
    (φ := ((80911/1000000 : ℚ) : ℝ) + ((0:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((80911/1000000 : ℚ)) : ℝ) 0).1,
    (cos_sin_shift (((80911/1000000 : ℚ)) : ℝ) 0).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_18_sign
end AxiomAudit
