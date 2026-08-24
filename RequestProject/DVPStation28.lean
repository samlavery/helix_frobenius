import RequestProject.DVPSqrtTable

/-!
# Station `t = 28` of the Hardy ladder (sign +)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT28 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((28 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((61361/250000 : ℚ) : ℝ))

theorem st28_c1 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((97003/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61361/1000000) (δ := 1/100000000) (ψ := 61361/250000) 28 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t1 : ((48499/50000 : ℚ) : ℝ) ≤ stT28 1 := by
  have hc : ((48499/50000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48499/50000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((48499/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c2 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((951377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 782803/10000000) (δ := 117/50000000) (ψ := 61361/250000) 28 3
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t2 : ((6726896955909/10000000000000 : ℚ) : ℝ) ≤ stT28 2 := by
  have hc : ((951327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6726896955909/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((951327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c3 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((621433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1125283/5000000) (δ := 51/20000000) (ψ := 61361/250000) 28 5
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t3 : ((1793777996633/5000000000000 : ℚ) : ℝ) ≤ stT28 3 := by
  have hc : ((621383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1793777996633/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((621383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c4 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((643537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136201/625000) (δ := 93/50000000) (ψ := 61361/250000) 28 6
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t4 : ((643487/2000000 : ℚ) : ℝ) ≤ stT28 4 := by
  have hc : ((643487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((643487/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((643487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c5 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((13401/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2091301/10000000) (δ := 123/50000000) (ψ := 61361/250000) 28 7
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t5 : ((59926609/200000000 : ℚ) : ℝ) ≤ stT28 5 := by
  have hc : ((67/100 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59926609/200000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((67/100 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c6 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((942199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -854153/10000000) (δ := 207/100000000) (ψ := 61361/250000) 28 8
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t6 : ((1923153166909/5000000000000 : ℚ) : ℝ) ≤ stT28 6 := by
  have hc : ((942149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1923153166909/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((942149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c7 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-134537/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5771569/10000000) (δ := 29/20000000) (ψ := 61361/250000) 28 9
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t7 : ((-101707979163/400000000000 : ℚ) : ℝ) ≤ stT28 7 := by
  have hc : ((-134547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101707979163/400000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-134547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c8 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((70041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3575629/10000000) (δ := 29/20000000) (ψ := 61361/250000) 28 9
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t8 : ((1933936551/39062500000 : ℚ) : ℝ) ≤ stT28 8 := by
  have hc : ((2188/15625 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1933936551/39062500000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((2188/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c9 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((15787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1943761/5000000) (δ := 229/100000000) (ψ := 61361/250000) 28 10
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t9 : ((52456661421/10000000000000 : ℚ) : ℝ) ≤ stT28 9 := by
  have hc : ((15737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52456661421/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((15737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c10 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((21851/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1743857/5000000) (δ := 269/100000000) (ψ := 61361/250000) 28 10
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t10 : ((276316601983/5000000000000 : ℚ) : ℝ) ≤ stT28 10 := by
  have hc : ((87379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276316601983/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((87379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c11 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-302043/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5548537/10000000) (δ := 199/100000000) (ψ := 61361/250000) 28 11
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t11 : ((-113846181969/625000000000 : ℚ) : ℝ) ≤ stT28 11 := by
  have hc : ((-75517/125000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113846181969/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-75517/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c12 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((122071/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27113/500000) (δ := 159/100000000) (ψ := 61361/250000) 28 11
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t12 : ((1409482156509/5000000000000 : ℚ) : ℝ) ≤ stT28 12 := by
  have hc : ((488259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1409482156509/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((488259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c13 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-193843/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6145249/10000000) (δ := 159/100000000) (ψ := 61361/250000) 28 11
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t13 : ((-1075316846211/5000000000000 : ℚ) : ℝ) ≤ stT28 13 := by
  have hc : ((-387711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1075316846211/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-387711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c14 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-178307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1093789/2500000) (δ := 193/100000000) (ψ := 61361/250000) 28 12
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t14 : ((-476679236841/10000000000000 : ℚ) : ℝ) ≤ stT28 14 := by
  have hc : ((-178357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476679236841/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-178357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c15 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((983531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90869/2000000) (δ := 273/100000000) (ψ := 61361/250000) 28 12
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t15 : ((634834035057/2500000000000 : ℚ) : ℝ) ≤ stT28 15 := by
  have hc : ((983481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634834035057/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((983481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c16 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-6343/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4972041/10000000) (δ := 233/100000000) (ψ := 61361/250000) 28 12
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t16 : ((-507502703001/5000000000000 : ℚ) : ℝ) ≤ stT28 16 := by
  have hc : ((-203001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507502703001/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-203001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c17 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-213819/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3246099/5000000) (δ := 71/50000000) (ψ := 61361/250000) 28 13
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t17 : ((-1037235450691/5000000000000 : ℚ) : ℝ) ≤ stT28 17 := by
  have hc : ((-427663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1037235450691/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-427663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c18 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((543291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2491109/10000000) (δ := 181/100000000) (ψ := 61361/250000) 28 13
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t18 : ((640215494151/5000000000000 : ℚ) : ℝ) ≤ stT28 18 := by
  have hc : ((543241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((640215494151/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((543241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c19 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((869089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323399/2500000) (δ := 221/100000000) (ψ := 61361/250000) 28 13
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t19 : ((1993711905123/10000000000000 : ℚ) : ℝ) ≤ stT28 19 := by
  have hc : ((869039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1993711905123/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((869039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c20 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-37357/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4884127/10000000) (δ := 221/100000000) (ψ := 61361/250000) 28 13
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t20 : ((-10442996577/125000000000 : ℚ) : ℝ) ≤ stT28 20 := by
  have hc : ((-18681/50000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10442996577/125000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-18681/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c21 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-984167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296341/400000) (δ := 171/100000000) (ψ := 61361/250000) 28 14
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t21 : ((-2147737668843/10000000000000 : ℚ) : ℝ) ≤ stT28 21 := by
  have hc : ((-984217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2147737668843/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-984217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c22 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-22483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1038031/2500000) (δ := 19/12500000) (ψ := 61361/250000) 28 14
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t22 : ((-11990146491/625000000000 : ℚ) : ℝ) ≤ stT28 22 := by
  have hc : ((-44991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11990146491/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-44991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c23 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((114329/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1040501/10000000) (δ := 251/100000000) (ψ := 61361/250000) 28 14
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t23 : ((119189698113/625000000000 : ℚ) : ℝ) ≤ stT28 23 := by
  have hc : ((457291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119189698113/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((457291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c24 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((714093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 121167/625000) (δ := 211/100000000) (ψ := 61361/250000) 28 14
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t24 : ((1457533847363/10000000000000 : ℚ) : ℝ) ≤ stT28 24 := by
  have hc : ((714043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1457533847363/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((714043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c25 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-170363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1199053/2500000) (δ := 211/100000000) (ψ := 61361/250000) 28 14
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t25 : ((-85194042597/1250000000000 : ℚ) : ℝ) ≤ stT28 25 := by
  have hc : ((-42597/125000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85194042597/1250000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-42597/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c26 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-992207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3770831/5000000) (δ := 171/100000000) (ψ := 61361/250000) 28 14
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t26 : ((-972988361317/5000000000000 : ℚ) : ℝ) ≤ stT28 26 := by
  have hc : ((-992257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-972988361317/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-992257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c27 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-596389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2762239/5000000) (δ := 101/50000000) (ψ := 61361/250000) 28 15
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t27 : ((-1147847451939/10000000000000 : ℚ) : ℝ) ≤ stT28 27 := by
  have hc : ((-596439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1147847451939/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-596439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c28 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((37027/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2978743/10000000) (δ := 241/100000000) (ψ := 61361/250000) 28 15
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t28 : ((17491247521/250000000000 : ℚ) : ℝ) ≤ stT28 28 := by
  have hc : ((18511/50000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17491247521/250000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((18511/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c29 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((978251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -522351/10000000) (δ := 201/100000000) (ψ := 61361/250000) 28 15
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t29 : ((1816473281553/10000000000000 : ℚ) : ℝ) ≤ stT28 29 := by
  have hc : ((978201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1816473281553/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((978201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c30 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((92283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 925379/5000000) (δ := 121/50000000) (ψ := 61361/250000) 28 15
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t30 : ((673893783287/5000000000000 : ℚ) : ℝ) ≤ stT28 30 := by
  have hc : ((369107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((673893783287/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((369107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c31 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-8751/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 829209/2000000) (δ := 281/100000000) (ψ := 61361/250000) 28 15
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t31 : ((-1965781103/125000000000 : ℚ) : ℝ) ≤ stT28 31 := by
  have hc : ((-2189/25000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1965781103/125000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-2189/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c32 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-82859/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3184227/5000000) (δ := 281/100000000) (ψ := 61361/250000) 28 15
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t32 : ((-9155265293/62500000000 : ℚ) : ℝ) ≤ stT28 32 := by
  have hc : ((-5179/6250 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9155265293/62500000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-5179/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c33 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-482231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7185493/10000000) (δ := 173/100000000) (ψ := 61361/250000) 28 16
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t33 : ((-52468759557/312500000000 : ℚ) : ℝ) ≤ stT28 33 := by
  have hc : ((-30141/31250 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52468759557/312500000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-30141/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c34 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-28167/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2547893/5000000) (δ := 23/10000000) (ψ := 61361/250000) 28 16
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t34 : ((-193245479973/2500000000000 : ℚ) : ℝ) ≤ stT28 34 := by
  have hc : ((-225361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193245479973/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-225361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c35 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((337381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533329/5000000) (δ := 173/100000000) (ψ := 61361/250000) 28 16
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t35 : ((142548321987/2500000000000 : ℚ) : ℝ) ≤ stT28 35 := by
  have hc : ((337331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142548321987/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((337331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c36 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((905653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1094697/10000000) (δ := 19/10000000) (ψ := 61361/250000) 28 16
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t36 : ((754668864799/5000000000000 : ℚ) : ℝ) ≤ stT28 36 := by
  have hc : ((905603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((754668864799/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((905603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c37 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((946271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12863/156250) (δ := 23/10000000) (ψ := 61361/250000) 28 16
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t37 : ((1555576915569/10000000000000 : ℚ) : ℝ) ≤ stT28 37 := by
  have hc : ((946221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1555576915569/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((946221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c38 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((474849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2690009/10000000) (δ := 173/100000000) (ψ := 61361/250000) 28 16
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t38 : ((385112792493/5000000000000 : ℚ) : ℝ) ≤ stT28 38 := by
  have hc : ((474799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((385112792493/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((474799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c39 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-230431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4508293/10000000) (δ := 3/2000000) (ψ := 61361/250000) 28 16
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t39 : ((-184532538321/5000000000000 : ℚ) : ℝ) ≤ stT28 39 := by
  have hc : ((-230481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184532538321/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-230481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c40 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-161679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 314027/500000) (δ := 173/100000000) (ψ := 61361/250000) 28 16
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t40 : ((-255652783771/2000000000000 : ℚ) : ℝ) ≤ stT28 40 := by
  have hc : ((-161689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255652783771/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-161689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c41 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-499039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7698941/10000000) (δ := 23/12500000) (ψ := 61361/250000) 28 17
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t41 : ((-48712950827/312500000000 : ℚ) : ℝ) ≤ stT28 41 := by
  have hc : ((-62383/62500 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48712950827/312500000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-62383/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c42 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-370329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -375757/625000) (δ := 219/100000000) (ψ := 61361/250000) 28 17
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t42 : ((-142867203509/1250000000000 : ℚ) : ℝ) ≤ stT28 42 := by
  have hc : ((-185177/250000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142867203509/1250000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-185177/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c43 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-1743/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4364977/10000000) (δ := 219/100000000) (ψ := 61361/250000) 28 17
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t43 : ((-2658813091/100000000000 : ℚ) : ℝ) ≤ stT28 43 := by
  have hc : ((-3487/20000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2658813091/100000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-3487/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c44 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((451559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2755711/10000000) (δ := 179/100000000) (ψ := 61361/250000) 28 17
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t44 : ((170168775501/2500000000000 : ℚ) : ℝ) ≤ stT28 44 := by
  have hc : ((451509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170168775501/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((451509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c45 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((178037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1182611/10000000) (δ := 33/12500000) (ψ := 61361/250000) 28 17
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t45 : ((265386807197/2000000000000 : ℚ) : ℝ) ≤ stT28 45 := by
  have hc : ((178027/200000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265386807197/2000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((178027/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c46 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((989883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44489/1250000) (δ := 33/12500000) (ψ := 61361/250000) 28 17
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t46 : ((1459428582027/10000000000000 : ℚ) : ℝ) ≤ stT28 46 := by
  have hc : ((989833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1459428582027/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((989833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c47 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((735401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1861347/10000000) (δ := 259/100000000) (ψ := 61361/250000) 28 17
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t47 : ((1072619000799/10000000000000 : ℚ) : ℝ) ≤ stT28 47 := by
  have hc : ((735351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1072619000799/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((735351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c48 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((234557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 667017/2000000) (δ := 259/100000000) (ψ := 61361/250000) 28 17
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t48 : ((2707852329/80000000000 : ℚ) : ℝ) ≤ stT28 48 := by
  have hc : ((234507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2707852329/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((234507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c49 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-20877/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955687/2000000) (δ := 33/12500000) (ψ := 61361/250000) 28 17
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t49 : ((-59657523863/1250000000000 : ℚ) : ℝ) ≤ stT28 49 := by
  have hc : ((-167041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59657523863/1250000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-167041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c50 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-787199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49541/80000) (δ := 259/100000000) (ψ := 61361/250000) 28 17
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t50 : ((-556669278643/5000000000000 : ℚ) : ℝ) ≤ stT28 50 := by
  have hc : ((-787249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-556669278643/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-787249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c51 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-993949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7578809/10000000) (δ := 179/100000000) (ψ := 61361/250000) 28 17
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t51 : ((-1391877913719/10000000000000 : ℚ) : ℝ) ≤ stT28 51 := by
  have hc : ((-993999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1391877913719/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-993999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c52 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-226861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6769889/10000000) (δ := 249/100000000) (ψ := 61361/250000) 28 18
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t52 : ((-629234105997/5000000000000 : ℚ) : ℝ) ≤ stT28 52 := by
  have hc : ((-453747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629234105997/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-453747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c53 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-567783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1087303/2000000) (δ := 249/100000000) (ψ := 61361/250000) 28 18
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t53 : ((-389989407899/5000000000000 : ℚ) : ℝ) ≤ stT28 53 := by
  have hc : ((-567833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389989407899/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-567833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c54 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-80343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2064033/5000000) (δ := 169/100000000) (ψ := 61361/250000) 28 18
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t54 : ((-27350261351/2500000000000 : ℚ) : ℝ) ≤ stT28 54 := by
  have hc : ((-80393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27350261351/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-80393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c55 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((41991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1421813/5000000) (δ := 117/50000000) (ψ := 61361/250000) 28 18
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t55 : ((28306940207/500000000000 : ℚ) : ℝ) ≤ stT28 55 := by
  have hc : ((20993/50000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28306940207/500000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((20993/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c56 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((806297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158233/1000000) (δ := 137/50000000) (ψ := 61361/250000) 28 18
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t56 : ((538696351791/5000000000000 : ℚ) : ℝ) ≤ stT28 56 := by
  have hc : ((806247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((538696351791/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((806247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c57 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((990583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073/31250) (δ := 97/50000000) (ψ := 61361/250000) 28 18
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t57 : ((327998163889/2500000000000 : ℚ) : ℝ) ≤ stT28 57 := by
  have hc : ((990533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327998163889/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((990533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c58 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((939501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437031/5000000) (δ := 249/100000000) (ψ := 61361/250000) 28 18
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t58 : ((154194910983/1250000000000 : ℚ) : ℝ) ≤ stT28 58 := by
  have hc : ((939451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154194910983/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((939451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c59 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((84519/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129417/625000) (δ := 169/100000000) (ψ := 61361/250000) 28 18
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t59 : ((440104878339/5000000000000 : ℚ) : ℝ) ≤ stT28 59 := by
  have hc : ((338051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440104878339/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((338051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c60 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((268589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3247171/10000000) (δ := 97/50000000) (ψ := 61361/250000) 28 18
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t60 : ((173341118883/5000000000000 : ℚ) : ℝ) ≤ stT28 60 := by
  have hc : ((268539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173341118883/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((268539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c61 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-37947/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2202111/5000000) (δ := 97/50000000) (ψ := 61361/250000) 28 18
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t61 : ((-48598966133/2000000000000 : ℚ) : ℝ) ≤ stT28 61 := by
  have hc : ((-37957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48598966133/2000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-37957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c62 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-301073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2771229/5000000) (δ := 117/50000000) (ψ := 61361/250000) 28 18
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t62 : ((-95598765549/1250000000000 : ℚ) : ℝ) ≤ stT28 62 := by
  have hc : ((-150549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95598765549/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-150549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c63 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-11107/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3331241/5000000) (δ := 209/100000000) (ψ := 61361/250000) 28 18
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t63 : ((-55977187201/500000000000 : ℚ) : ℝ) ≤ stT28 63 := by
  have hc : ((-88861/100000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55977187201/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-88861/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c64 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-199873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7764867/10000000) (δ := 117/50000000) (ψ := 61361/250000) 28 18
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t64 : ((-249853949883/2000000000000 : ℚ) : ℝ) ≤ stT28 64 := by
  have hc : ((-199883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249853949883/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-199883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c65 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-184331/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6857803/10000000) (δ := 41/20000000) (ψ := 61361/250000) 28 19
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t65 : ((-57161747667/500000000000 : ℚ) : ℝ) ≤ stT28 65 := by
  have hc : ((-184341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57161747667/500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-184341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c66 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-677851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144727/250000) (δ := 79/50000000) (ψ := 61361/250000) 28 19
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t66 : ((-166887701883/2000000000000 : ℚ) : ℝ) ≤ stT28 66 := by
  have hc : ((-677901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166887701883/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-677901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c67 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-79537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4736429/10000000) (δ := 119/50000000) (ψ := 61361/250000) 28 19
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t67 : ((-38874090561/1000000000000 : ℚ) : ℝ) ≤ stT28 67 := by
  have hc : ((-159099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38874090561/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-159099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c68 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((90921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3699373/10000000) (δ := 139/50000000) (ψ := 61361/250000) 28 19
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t68 : ((55098631269/5000000000000 : ℚ) : ℝ) ≤ stT28 68 := by
  have hc : ((90871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55098631269/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((90871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c69 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((239631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2677457/10000000) (δ := 139/50000000) (ψ := 61361/250000) 28 19
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t69 : ((72112899987/1250000000000 : ℚ) : ℝ) ≤ stT28 69 := by
  have hc : ((119803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72112899987/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((119803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c70 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((785001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334049/2000000) (δ := 79/50000000) (ψ := 61361/250000) 28 19
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t70 : ((234548853457/2500000000000 : ℚ) : ℝ) ≤ stT28 70 := by
  have hc : ((784951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234548853457/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((784951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c71 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((963523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677321/10000000) (δ := 41/20000000) (ψ := 61361/250000) 28 19
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t71 : ((1143431450413/10000000000000 : ℚ) : ℝ) ≤ stT28 71 := by
  have hc : ((963473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1143431450413/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((963473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c72 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((496363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75429/2500000) (δ := 119/50000000) (ψ := 61361/250000) 28 19
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t72 : ((292469896359/2500000000000 : ℚ) : ℝ) ≤ stT28 72 := by
  have hc : ((248169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292469896359/2500000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((248169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c73 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((437127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1267249/10000000) (δ := 79/50000000) (ψ := 61361/250000) 28 19
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t73 : ((255794494461/2500000000000 : ℚ) : ℝ) ≤ stT28 73 := by
  have hc : ((218551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255794494461/2500000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((218551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c74 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((25243/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554911/2500000) (δ := 49/20000000) (ψ := 61361/250000) 28 19
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t74 : ((7335514179/100000000000 : ℚ) : ℝ) ≤ stT28 74 := by
  have hc : ((25241/40000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7335514179/100000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((25241/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c75 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((30229/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 394907/1250000) (δ := 119/50000000) (ψ := 61361/250000) 28 19
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t75 : ((21812283/625000000 : ℚ) : ℝ) ≤ stT28 75 := by
  have hc : ((1889/6250 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21812283/625000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((1889/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c76 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-63729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2043211/5000000) (δ := 79/50000000) (ψ := 61361/250000) 28 19
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t76 : ((-73159551541/10000000000000 : ℚ) : ℝ) ≤ stT28 76 := by
  have hc : ((-63779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73159551541/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-63779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c77 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-10417/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5001467/10000000) (δ := 119/50000000) (ψ := 61361/250000) 28 19
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t77 : ((-23745400419/500000000000 : ℚ) : ℝ) ≤ stT28 77 := by
  have hc : ((-41673/100000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23745400419/500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-41673/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c78 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-711117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2952353/5000000) (δ := 99/50000000) (ψ := 61361/250000) 28 19
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t78 : ((-402619374213/5000000000000 : ℚ) : ℝ) ≤ stT28 78 := by
  have hc : ((-711167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-402619374213/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-711167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c79 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-455927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3398219/5000000) (δ := 33/20000000) (ψ := 61361/250000) 28 19
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t79 : ((-1001926023/9765625000 : ℚ) : ℝ) ≤ stT28 79 := by
  have hc : ((-28497/31250 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1001926023/9765625000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-28497/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c80 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-498747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959619/1250000) (δ := 99/50000000) (ψ := 61361/250000) 28 19
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t80 : ((-69705506781/625000000000 : ℚ) : ℝ) ≤ stT28 80 := by
  have hc : ((-124693/125000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69705506781/625000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-124693/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c81 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-1539/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1432287/2000000) (δ := 147/100000000) (ψ := 61361/250000) 28 20
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t81 : ((-5344032053/50000000000 : ℚ) : ℝ) ≤ stT28 81 := by
  have hc : ((-38477/40000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5344032053/50000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-38477/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c82 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-40677/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98477/156250) (δ := 147/100000000) (ψ := 61361/250000) 28 20
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t82 : ((-22461511361/250000000000 : ℚ) : ℝ) ≤ stT28 82 := by
  have hc : ((-81359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22461511361/250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-81359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c83 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-573537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5454033/10000000) (δ := 267/100000000) (ψ := 61361/250000) 28 20
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t83 : ((-629593755441/10000000000000 : ℚ) : ℝ) ≤ stT28 83 := by
  have hc : ((-573587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629593755441/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-573587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c84 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((-68003/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4615699/10000000) (δ := 37/12500000) (ψ := 61361/250000) 28 20
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t84 : ((-14842206379/500000000000 : ℚ) : ℝ) ≤ stT28 84 := by
  have hc : ((-136031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14842206379/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-136031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c85 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((13963/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3787287/10000000) (δ := 11/6250000) (ψ := 61361/250000) 28 20
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t85 : ((7565718863/1250000000000 : ℚ) : ℝ) ≤ stT28 85 := by
  have hc : ((27901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7565718863/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((27901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_c86 :
    |Real.cos (((28 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((61361/250000 : ℚ) : ℝ))
      - ((11689/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -593713/2000000) (δ := 1/390625) (ψ := 61361/250000) 28 20
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st28_t86 : ((201646070673/5000000000000 : ℚ) : ℝ) ≤ stT28 86 := by
  have hc : ((186999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((28 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((61361/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st28_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201646070673/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((186999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st28_p1 : ((48499/50000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT28 (i+1) := by
  rw [Finset.sum_range_one]
  exact st28_t1

theorem st28_p2 : ((16426696955909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT28 (i+1))
      = (∑ i ∈ Finset.range 1, stT28 (i+1)) + stT28 2 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 1
    simpa using h
  have hprev := st28_p1
  have hstep := st28_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p3 : ((800570117967/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT28 (i+1))
      = (∑ i ∈ Finset.range 2, stT28 (i+1)) + stT28 3 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 2
    simpa using h
  have hprev := st28_p2
  have hstep := st28_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p4 : ((929267517967/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT28 (i+1))
      = (∑ i ∈ Finset.range 3, stT28 (i+1)) + stT28 4 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 3
    simpa using h
  have hprev := st28_p3
  have hstep := st28_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p5 : ((1049120735967/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT28 (i+1))
      = (∑ i ∈ Finset.range 4, stT28 (i+1)) + stT28 5 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 4
    simpa using h
  have hprev := st28_p4
  have hstep := st28_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p6 : ((30074324732993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT28 (i+1))
      = (∑ i ∈ Finset.range 5, stT28 (i+1)) + stT28 6 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 5
    simpa using h
  have hprev := st28_p5
  have hstep := st28_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p7 : ((13765812626959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT28 (i+1))
      = (∑ i ∈ Finset.range 6, stT28 (i+1)) + stT28 7 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 6
    simpa using h
  have hprev := st28_p6
  have hstep := st28_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p8 : ((14013356505487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT28 (i+1))
      = (∑ i ∈ Finset.range 7, stT28 (i+1)) + stT28 8 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 7
    simpa using h
  have hprev := st28_p7
  have hstep := st28_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p9 : ((5615833934479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT28 (i+1))
      = (∑ i ∈ Finset.range 8, stT28 (i+1)) + stT28 9 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 8
    simpa using h
  have hprev := st28_p8
  have hstep := st28_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p10 : ((28631802876361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT28 (i+1))
      = (∑ i ∈ Finset.range 9, stT28 (i+1)) + stT28 10 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 9
    simpa using h
  have hprev := st28_p9
  have hstep := st28_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p11 : ((26810263964857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT28 (i+1))
      = (∑ i ∈ Finset.range 10, stT28 (i+1)) + stT28 11 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 10
    simpa using h
  have hprev := st28_p10
  have hstep := st28_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p12 : ((237033826223/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT28 (i+1))
      = (∑ i ∈ Finset.range 11, stT28 (i+1)) + stT28 12 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 11
    simpa using h
  have hprev := st28_p11
  have hstep := st28_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p13 : ((27478594585453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT28 (i+1))
      = (∑ i ∈ Finset.range 12, stT28 (i+1)) + stT28 13 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 12
    simpa using h
  have hprev := st28_p12
  have hstep := st28_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p14 : ((6750478837153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT28 (i+1))
      = (∑ i ∈ Finset.range 13, stT28 (i+1)) + stT28 14 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 13
    simpa using h
  have hprev := st28_p13
  have hstep := st28_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p15 : ((738531287221/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT28 (i+1))
      = (∑ i ∈ Finset.range 14, stT28 (i+1)) + stT28 15 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 14
    simpa using h
  have hprev := st28_p14
  have hstep := st28_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p16 : ((14263123041419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT28 (i+1))
      = (∑ i ∈ Finset.range 15, stT28 (i+1)) + stT28 16 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 15
    simpa using h
  have hprev := st28_p15
  have hstep := st28_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p17 : ((1653235948841/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT28 (i+1))
      = (∑ i ∈ Finset.range 16, stT28 (i+1)) + stT28 17 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 16
    simpa using h
  have hprev := st28_p16
  have hstep := st28_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p18 : ((13866103084879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT28 (i+1))
      = (∑ i ∈ Finset.range 17, stT28 (i+1)) + stT28 18 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 17
    simpa using h
  have hprev := st28_p17
  have hstep := st28_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p19 : ((29725918074881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT28 (i+1))
      = (∑ i ∈ Finset.range 18, stT28 (i+1)) + stT28 19 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 18
    simpa using h
  have hprev := st28_p18
  have hstep := st28_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p20 : ((28890478348721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT28 (i+1))
      = (∑ i ∈ Finset.range 19, stT28 (i+1)) + stT28 20 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 19
    simpa using h
  have hprev := st28_p19
  have hstep := st28_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p21 : ((13371370339939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT28 (i+1))
      = (∑ i ∈ Finset.range 20, stT28 (i+1)) + stT28 21 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 20
    simpa using h
  have hprev := st28_p20
  have hstep := st28_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p22 : ((13275449168011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT28 (i+1))
      = (∑ i ∈ Finset.range 21, stT28 (i+1)) + stT28 22 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 21
    simpa using h
  have hprev := st28_p21
  have hstep := st28_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p23 : ((2845793350583/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT28 (i+1))
      = (∑ i ∈ Finset.range 22, stT28 (i+1)) + stT28 23 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 22
    simpa using h
  have hprev := st28_p22
  have hstep := st28_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p24 : ((29915467353193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT28 (i+1))
      = (∑ i ∈ Finset.range 23, stT28 (i+1)) + stT28 24 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 23
    simpa using h
  have hprev := st28_p23
  have hstep := st28_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p25 : ((29233915012417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT28 (i+1))
      = (∑ i ∈ Finset.range 24, stT28 (i+1)) + stT28 25 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 24
    simpa using h
  have hprev := st28_p24
  have hstep := st28_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p26 : ((27287938289783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT28 (i+1))
      = (∑ i ∈ Finset.range 25, stT28 (i+1)) + stT28 26 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 25
    simpa using h
  have hprev := st28_p25
  have hstep := st28_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p27 : ((6535022709461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT28 (i+1))
      = (∑ i ∈ Finset.range 26, stT28 (i+1)) + stT28 27 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 26
    simpa using h
  have hprev := st28_p26
  have hstep := st28_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p28 : ((6709935184671/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT28 (i+1))
      = (∑ i ∈ Finset.range 27, stT28 (i+1)) + stT28 28 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 27
    simpa using h
  have hprev := st28_p27
  have hstep := st28_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p29 : ((28656214020237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT28 (i+1))
      = (∑ i ∈ Finset.range 28, stT28 (i+1)) + stT28 29 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 28
    simpa using h
  have hprev := st28_p28
  have hstep := st28_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p30 : ((30004001586811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT28 (i+1))
      = (∑ i ∈ Finset.range 29, stT28 (i+1)) + stT28 30 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 29
    simpa using h
  have hprev := st28_p29
  have hstep := st28_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p31 : ((29846739098571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT28 (i+1))
      = (∑ i ∈ Finset.range 30, stT28 (i+1)) + stT28 31 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 30
    simpa using h
  have hprev := st28_p30
  have hstep := st28_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p32 : ((28381896651691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT28 (i+1))
      = (∑ i ∈ Finset.range 31, stT28 (i+1)) + stT28 32 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 31
    simpa using h
  have hprev := st28_p31
  have hstep := st28_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p33 : ((26702896345867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT28 (i+1))
      = (∑ i ∈ Finset.range 32, stT28 (i+1)) + stT28 33 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 32
    simpa using h
  have hprev := st28_p32
  have hstep := st28_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p34 : ((1037196577039/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT28 (i+1))
      = (∑ i ∈ Finset.range 33, stT28 (i+1)) + stT28 34 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 33
    simpa using h
  have hprev := st28_p33
  have hstep := st28_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p35 : ((26500107713923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT28 (i+1))
      = (∑ i ∈ Finset.range 34, stT28 (i+1)) + stT28 35 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 34
    simpa using h
  have hprev := st28_p34
  have hstep := st28_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p36 : ((28009445443521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT28 (i+1))
      = (∑ i ∈ Finset.range 35, stT28 (i+1)) + stT28 36 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 35
    simpa using h
  have hprev := st28_p35
  have hstep := st28_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p37 : ((2956502235909/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT28 (i+1))
      = (∑ i ∈ Finset.range 36, stT28 (i+1)) + stT28 37 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 36
    simpa using h
  have hprev := st28_p36
  have hstep := st28_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p38 : ((7583811986019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT28 (i+1))
      = (∑ i ∈ Finset.range 37, stT28 (i+1)) + stT28 38 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 37
    simpa using h
  have hprev := st28_p37
  have hstep := st28_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p39 : ((14983091433717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT28 (i+1))
      = (∑ i ∈ Finset.range 38, stT28 (i+1)) + stT28 39 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 38
    simpa using h
  have hprev := st28_p38
  have hstep := st28_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p40 : ((28687918948579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT28 (i+1))
      = (∑ i ∈ Finset.range 39, stT28 (i+1)) + stT28 40 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 39
    simpa using h
  have hprev := st28_p39
  have hstep := st28_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p41 : ((5425820904423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT28 (i+1))
      = (∑ i ∈ Finset.range 40, stT28 (i+1)) + stT28 41 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 40
    simpa using h
  have hprev := st28_p40
  have hstep := st28_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p42 : ((25986166894043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT28 (i+1))
      = (∑ i ∈ Finset.range 41, stT28 (i+1)) + stT28 42 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 41
    simpa using h
  have hprev := st28_p41
  have hstep := st28_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p43 : ((25720285584943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT28 (i+1))
      = (∑ i ∈ Finset.range 42, stT28 (i+1)) + stT28 43 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 42
    simpa using h
  have hprev := st28_p42
  have hstep := st28_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p44 : ((26400960686947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT28 (i+1))
      = (∑ i ∈ Finset.range 43, stT28 (i+1)) + stT28 44 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 43
    simpa using h
  have hprev := st28_p43
  have hstep := st28_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p45 : ((6931973680733/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT28 (i+1))
      = (∑ i ∈ Finset.range 44, stT28 (i+1)) + stT28 45 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 44
    simpa using h
  have hprev := st28_p44
  have hstep := st28_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p46 : ((29187323304959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT28 (i+1))
      = (∑ i ∈ Finset.range 45, stT28 (i+1)) + stT28 46 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 45
    simpa using h
  have hprev := st28_p45
  have hstep := st28_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p47 : ((15129971152879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT28 (i+1))
      = (∑ i ∈ Finset.range 46, stT28 (i+1)) + stT28 47 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 46
    simpa using h
  have hprev := st28_p46
  have hstep := st28_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p48 : ((30598423846883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT28 (i+1))
      = (∑ i ∈ Finset.range 47, stT28 (i+1)) + stT28 48 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 47
    simpa using h
  have hprev := st28_p47
  have hstep := st28_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p49 : ((30121163655979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT28 (i+1))
      = (∑ i ∈ Finset.range 48, stT28 (i+1)) + stT28 49 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 48
    simpa using h
  have hprev := st28_p48
  have hstep := st28_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p50 : ((29007825098693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT28 (i+1))
      = (∑ i ∈ Finset.range 49, stT28 (i+1)) + stT28 50 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 49
    simpa using h
  have hprev := st28_p49
  have hstep := st28_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p51 : ((13807973592487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT28 (i+1))
      = (∑ i ∈ Finset.range 50, stT28 (i+1)) + stT28 51 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 50
    simpa using h
  have hprev := st28_p50
  have hstep := st28_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p52 : ((1317873948649/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT28 (i+1))
      = (∑ i ∈ Finset.range 51, stT28 (i+1)) + stT28 52 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 51
    simpa using h
  have hprev := st28_p51
  have hstep := st28_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p53 : ((12788750078591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT28 (i+1))
      = (∑ i ∈ Finset.range 52, stT28 (i+1)) + stT28 53 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 52
    simpa using h
  have hprev := st28_p52
  have hstep := st28_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p54 : ((12734049555889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT28 (i+1))
      = (∑ i ∈ Finset.range 53, stT28 (i+1)) + stT28 54 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 53
    simpa using h
  have hprev := st28_p53
  have hstep := st28_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p55 : ((13017118957959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT28 (i+1))
      = (∑ i ∈ Finset.range 54, stT28 (i+1)) + stT28 55 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 54
    simpa using h
  have hprev := st28_p54
  have hstep := st28_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p56 : ((54223261239/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT28 (i+1))
      = (∑ i ∈ Finset.range 55, stT28 (i+1)) + stT28 56 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 55
    simpa using h
  have hprev := st28_p55
  have hstep := st28_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p57 : ((1776476454691/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT28 (i+1))
      = (∑ i ∈ Finset.range 56, stT28 (i+1)) + stT28 57 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 56
    simpa using h
  have hprev := st28_p56
  have hstep := st28_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p58 : ((741429564073/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT28 (i+1))
      = (∑ i ∈ Finset.range 57, stT28 (i+1)) + stT28 58 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 57
    simpa using h
  have hprev := st28_p57
  have hstep := st28_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p59 : ((15268696159799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT28 (i+1))
      = (∑ i ∈ Finset.range 58, stT28 (i+1)) + stT28 59 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 58
    simpa using h
  have hprev := st28_p58
  have hstep := st28_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p60 : ((7721018639341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT28 (i+1))
      = (∑ i ∈ Finset.range 59, stT28 (i+1)) + stT28 60 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 59
    simpa using h
  have hprev := st28_p59
  have hstep := st28_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p61 : ((30641079726699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT28 (i+1))
      = (∑ i ∈ Finset.range 60, stT28 (i+1)) + stT28 61 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 60
    simpa using h
  have hprev := st28_p60
  have hstep := st28_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p62 : ((29876289602307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT28 (i+1))
      = (∑ i ∈ Finset.range 61, stT28 (i+1)) + stT28 62 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 61
    simpa using h
  have hprev := st28_p61
  have hstep := st28_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p63 : ((28756745858287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT28 (i+1))
      = (∑ i ∈ Finset.range 62, stT28 (i+1)) + stT28 63 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 62
    simpa using h
  have hprev := st28_p62
  have hstep := st28_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p64 : ((3438434513609/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT28 (i+1))
      = (∑ i ∈ Finset.range 63, stT28 (i+1)) + stT28 64 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 63
    simpa using h
  have hprev := st28_p63
  have hstep := st28_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p65 : ((6591060288883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT28 (i+1))
      = (∑ i ∈ Finset.range 64, stT28 (i+1)) + stT28 65 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 64
    simpa using h
  have hprev := st28_p64
  have hstep := st28_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p66 : ((25529802646117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT28 (i+1))
      = (∑ i ∈ Finset.range 65, stT28 (i+1)) + stT28 66 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 65
    simpa using h
  have hprev := st28_p65
  have hstep := st28_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p67 : ((25141061740507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT28 (i+1))
      = (∑ i ∈ Finset.range 66, stT28 (i+1)) + stT28 67 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 66
    simpa using h
  have hprev := st28_p66
  have hstep := st28_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p68 : ((5050251800609/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT28 (i+1))
      = (∑ i ∈ Finset.range 67, stT28 (i+1)) + stT28 68 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 67
    simpa using h
  have hprev := st28_p67
  have hstep := st28_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p69 : ((25828162202941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT28 (i+1))
      = (∑ i ∈ Finset.range 68, stT28 (i+1)) + stT28 69 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 68
    simpa using h
  have hprev := st28_p68
  have hstep := st28_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p70 : ((26766357616769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT28 (i+1))
      = (∑ i ∈ Finset.range 69, stT28 (i+1)) + stT28 70 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 69
    simpa using h
  have hprev := st28_p69
  have hstep := st28_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p71 : ((13954894533591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT28 (i+1))
      = (∑ i ∈ Finset.range 70, stT28 (i+1)) + stT28 71 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 70
    simpa using h
  have hprev := st28_p70
  have hstep := st28_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p72 : ((14539834326309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT28 (i+1))
      = (∑ i ∈ Finset.range 71, stT28 (i+1)) + stT28 72 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 71
    simpa using h
  have hprev := st28_p71
  have hstep := st28_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p73 : ((15051423315231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT28 (i+1))
      = (∑ i ∈ Finset.range 72, stT28 (i+1)) + stT28 73 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 72
    simpa using h
  have hprev := st28_p72
  have hstep := st28_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p74 : ((15418199024181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT28 (i+1))
      = (∑ i ∈ Finset.range 73, stT28 (i+1)) + stT28 74 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 73
    simpa using h
  have hprev := st28_p73
  have hstep := st28_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p75 : ((15592697288181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT28 (i+1))
      = (∑ i ∈ Finset.range 74, stT28 (i+1)) + stT28 75 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 74
    simpa using h
  have hprev := st28_p74
  have hstep := st28_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p76 : ((31112235024821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT28 (i+1))
      = (∑ i ∈ Finset.range 75, stT28 (i+1)) + stT28 76 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 75
    simpa using h
  have hprev := st28_p75
  have hstep := st28_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p77 : ((30637327016441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT28 (i+1))
      = (∑ i ∈ Finset.range 76, stT28 (i+1)) + stT28 77 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 76
    simpa using h
  have hprev := st28_p76
  have hstep := st28_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p78 : ((5966417653603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT28 (i+1))
      = (∑ i ∈ Finset.range 77, stT28 (i+1)) + stT28 78 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 77
    simpa using h
  have hprev := st28_p77
  have hstep := st28_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p79 : ((28806116020463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT28 (i+1))
      = (∑ i ∈ Finset.range 78, stT28 (i+1)) + stT28 79 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 78
    simpa using h
  have hprev := st28_p78
  have hstep := st28_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p80 : ((27690827911967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT28 (i+1))
      = (∑ i ∈ Finset.range 79, stT28 (i+1)) + stT28 80 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 79
    simpa using h
  have hprev := st28_p79
  have hstep := st28_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p81 : ((26622021501367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT28 (i+1))
      = (∑ i ∈ Finset.range 80, stT28 (i+1)) + stT28 81 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 80
    simpa using h
  have hprev := st28_p80
  have hstep := st28_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p82 : ((25723561046927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT28 (i+1))
      = (∑ i ∈ Finset.range 81, stT28 (i+1)) + stT28 82 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 81
    simpa using h
  have hprev := st28_p81
  have hstep := st28_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p83 : ((12546983645743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT28 (i+1))
      = (∑ i ∈ Finset.range 82, stT28 (i+1)) + stT28 83 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 82
    simpa using h
  have hprev := st28_p82
  have hstep := st28_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p84 : ((12398561581953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT28 (i+1))
      = (∑ i ∈ Finset.range 83, stT28 (i+1)) + stT28 84 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 83
    simpa using h
  have hprev := st28_p83
  have hstep := st28_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p85 : ((2485764891481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT28 (i+1))
      = (∑ i ∈ Finset.range 84, stT28 (i+1)) + stT28 85 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 84
    simpa using h
  have hprev := st28_p84
  have hstep := st28_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st28_p86 : ((6315235264039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT28 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT28 (i+1))
      = (∑ i ∈ Finset.range 85, stT28 (i+1)) + stT28 86 := by
    have h := Finset.sum_range_succ (fun i => stT28 (i+1)) 85
    simpa using h
  have hprev := st28_p85
  have hstep := st28_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 28`.** -/
theorem station_28_sign : 0 < hardyG (((28:ℕ)):ℝ) := by
  have hcore := phase_station_lower 28 86 (by norm_num) (by norm_num)
    ((61361/250000 : ℚ) : ℝ)
  have hchain := st28_p86
  have hbridge : (∑ i ∈ Finset.range 86, stT28 (i+1))
      = ∑ i ∈ Finset.range 86,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((28:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((61361/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_86
  have hsh := rpow_half_shifts (N := 86) (by norm_num)
  have hcost : ((86:ℕ):ℝ) ^ ((1/2:ℝ)) / (((28:ℕ)):ℝ)
      + ((86:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((28:ℕ)):ℝ)+1) * ((((28:ℕ)):ℝ)+2) / 8
        * (((86:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((86:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((4945346999/10354400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6315235264039/2500000000000 : ℚ) : ℝ) - ((4945346999/10354400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((61361/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((28:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((61361/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((28:ℕ)):ℝ))).re
      - Real.sin ((61361/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((28:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (((28:ℕ)):ℝ)) (T := (30:ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((28:ℕ)):ℝ)
      = ((((28:ℕ)):ℝ) * (Real.log (((28:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((28:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_28
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
  have hθwin : |(((61361/250000 : ℚ) : ℝ) + ((1:ℤ)) * (2*Real.pi)) - theta (((28:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((28:ℕ)):ℝ))
    (φ := ((61361/250000 : ℚ) : ℝ) + ((1:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((61361/250000 : ℚ)) : ℝ) 1).1,
    (cos_sin_shift (((61361/250000 : ℚ)) : ℝ) 1).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_28_sign
end AxiomAudit
