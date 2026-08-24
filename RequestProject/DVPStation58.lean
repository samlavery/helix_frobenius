import RequestProject.DVPSqrtTable

/-!
# Station `t = 58` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT58 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((58 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((504553/1000000 : ℚ) : ℝ))

theorem st58_c1 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((875391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -630691/5000000) (δ := 21/100000000) (ψ := 504553/1000000) 58 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t1 : ((875341/1000000 : ℚ) : ℝ) ≤ stT58 1 := by
  have hc : ((875341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((875341/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((875341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c2 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-415121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4997179/10000000) (δ := 233/50000000) (ψ := 504553/1000000) 58 6
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t2 : ((-733925593157/2500000000000 : ℚ) : ℝ) ≤ stT58 2 := by
  have hc : ((-415171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-733925593157/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-415171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c3 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((231877/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 957767/10000000) (δ := 529/100000000) (ψ := 504553/1000000) 58 10
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t3 : ((1338670154479/2500000000000 : ℚ) : ℝ) ≤ stT58 3 := by
  have hc : ((463729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1338670154479/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((463729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c4 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-208551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4452223/10000000) (δ := 341/100000000) (ψ := 504553/1000000) 58 13
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t4 : ((-1043005208601/10000000000000 : ℚ) : ℝ) ≤ stT58 4 := by
  have hc : ((-208601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1043005208601/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-208601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c5 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((165103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1756167/5000000) (δ := 501/100000000) (ψ := 504553/1000000) 58 15
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t5 : ((147627859631/2000000000000 : ℚ) : ℝ) ≤ stT58 5 := by
  have hc : ((165053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147627859631/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((165053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c6 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-30239/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 902041/1250000) (δ := 393/100000000) (ψ := 504553/1000000) 58 16
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t6 : ((-1975305317067/5000000000000 : ℚ) : ℝ) ≤ stT58 6 := by
  have hc : ((-483849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1975305317067/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-483849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c7 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((29563/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7391/40000) (δ := 309/100000000) (ψ := 504553/1000000) 58 18
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t7 : ((27932514071/100000000000 : ℚ) : ℝ) ≤ stT58 7 := by
  have hc : ((29561/40000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27932514071/100000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((29561/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c8 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((750131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1806339/10000000) (δ := 169/50000000) (ψ := 504553/1000000) 58 19
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t8 : ((2651936128173/10000000000000 : ℚ) : ℝ) ≤ stT58 8 := by
  have hc : ((750081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2651936128173/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((750081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c9 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((295549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 794229/2500000) (δ := 57/12500000) (ψ := 504553/1000000) 58 20
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t9 : ((984996568167/10000000000000 : ℚ) : ℝ) ≤ stT58 9 := by
  have hc : ((295499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((984996568167/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((295499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c10 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((454941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2746227/10000000) (δ := 527/100000000) (ψ := 504553/1000000) 58 21
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t10 : ((1438491346807/10000000000000 : ℚ) : ℝ) ≤ stT58 10 := by
  have hc : ((454891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1438491346807/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((454891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c11 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((18833/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1341/15625) (δ := 417/100000000) (ψ := 504553/1000000) 58 22
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t11 : ((3548788001/12500000000 : ℚ) : ℝ) ≤ stT58 11 := by
  have hc : ((1177/1250 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3548788001/12500000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((1177/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c12 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((626899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2233073/10000000) (δ := 77/25000000) (ψ := 504553/1000000) 58 23
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t12 : ((1809556977599/10000000000000 : ℚ) : ℝ) ≤ stT58 12 := by
  have hc : ((626849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1809556977599/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((626849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c13 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-820989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1583711/2500000) (δ := 339/100000000) (ψ := 504553/1000000) 58 24
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t13 : ((-2277152487539/10000000000000 : ℚ) : ℝ) ≤ stT58 13 := by
  have hc : ((-821039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2277152487539/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-821039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c14 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-192323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1102703/2500000) (δ := 101/25000000) (ψ := 504553/1000000) 58 24
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t14 : ((-514138580649/10000000000000 : ℚ) : ℝ) ≤ stT58 14 := by
  have hc : ((-192373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-514138580649/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-192373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c15 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((86917/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258637/2000000) (δ := 287/50000000) (ψ := 504553/1000000) 58 25
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t15 : ((438292463/1953125000 : ℚ) : ℝ) ≤ stT58 15 := by
  have hc : ((2716/3125 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438292463/1953125000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((2716/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c16 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-996443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7643063/10000000) (δ := 463/100000000) (ψ := 504553/1000000) 58 26
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t16 : ((-2491233496493/10000000000000 : ℚ) : ℝ) ≤ stT58 16 := by
  have hc : ((-996493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2491233496493/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-996493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c17 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((179299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1147507/10000000) (δ := 343/100000000) (ψ := 504553/1000000) 58 26
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t17 : ((108709912971/500000000000 : ℚ) : ℝ) ≤ stT58 17 := by
  have hc : ((179289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108709912971/500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((179289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c18 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-403247/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3136243/5000000) (δ := 331/100000000) (ψ := 504553/1000000) 58 27
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t18 : ((-118815172407/625000000000 : ℚ) : ℝ) ≤ stT58 18 := by
  have hc : ((-50409/62500 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118815172407/625000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-50409/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c19 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((809847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1567261/10000000) (δ := 451/100000000) (ψ := 504553/1000000) 58 27
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t19 : ((1857801456129/10000000000000 : ℚ) : ℝ) ≤ stT58 19 := by
  have hc : ((809797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1857801456129/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((809797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c20 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-895909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3351587/5000000) (δ := 221/50000000) (ψ := 504553/1000000) 58 28
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t20 : ((-500856312303/2500000000000 : ℚ) : ℝ) ≤ stT58 20 := by
  have hc : ((-895959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500856312303/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-895959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c21 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((197797/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371399/10000000) (δ := 381/100000000) (ψ := 504553/1000000) 58 28
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t21 : ((215803220043/1000000000000 : ℚ) : ℝ) ≤ stT58 21 := by
  have hc : ((197787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215803220043/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((197787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c22 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-956839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3558401/5000000) (δ := 161/50000000) (ψ := 504553/1000000) 58 28
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t22 : ((-255011875389/1250000000000 : ℚ) : ℝ) ≤ stT58 22 := by
  have hc : ((-956889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255011875389/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-956889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c23 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((653753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268207/1250000) (δ := 491/100000000) (ψ := 504553/1000000) 58 29
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t23 : ((170383111029/1250000000000 : ℚ) : ℝ) ≤ stT58 23 := by
  have hc : ((653703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((170383111029/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((653703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c24 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-39389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251593/625000) (δ := 411/100000000) (ψ := 504553/1000000) 58 29
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t24 : ((-40252271619/5000000000000 : ℚ) : ℝ) ≤ stT58 24 := by
  have hc : ((-39439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40252271619/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-39439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c25 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-67023/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2881643/5000000) (δ := 11/2500000) (ψ := 504553/1000000) 58 30
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t25 : ((-33514016757/250000000000 : ℚ) : ℝ) ≤ stT58 25 := by
  have hc : ((-16757/25000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33514016757/250000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-16757/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c26 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((199907/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76283/10000000) (δ := 19/5000000) (ψ := 504553/1000000) 58 30
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t26 : ((392030200417/2000000000000 : ℚ) : ℝ) ≤ stT58 26 := by
  have hc : ((199897/200000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((392030200417/2000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((199897/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c27 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-55439/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1079213/2000000) (δ := 383/100000000) (ψ := 504553/1000000) 58 30
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t27 : ((-26675508361/250000000000 : ℚ) : ℝ) ≤ stT58 27 := by
  have hc : ((-13861/25000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26675508361/250000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-13861/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c28 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-430133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -503859/1000000) (δ := 529/100000000) (ψ := 504553/1000000) 58 31
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t28 : ((-812969727609/10000000000000 : ℚ) : ℝ) ≤ stT58 28 := by
  have hc : ((-430183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812969727609/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-430183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c29 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((999803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12413/2500000) (δ := 389/100000000) (ψ := 504553/1000000) 58 31
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t29 : ((1856494332609/10000000000000 : ℚ) : ℝ) ≤ stT58 29 := by
  have hc : ((999753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1856494332609/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((999753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c30 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-201757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4965377/10000000) (δ := 247/50000000) (ψ := 504553/1000000) 58 31
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t30 : ((-92100468061/1250000000000 : ℚ) : ℝ) ≤ stT58 30 := by
  have hc : ((-100891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92100468061/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-100891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c31 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-9177/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2994031/5000000) (δ := 539/100000000) (ψ := 504553/1000000) 58 32
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t31 : ((-65934040367/500000000000 : ℚ) : ℝ) ≤ stT58 31 := by
  have hc : ((-73421/100000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65934040367/500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-73421/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c32 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((212633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1384501/10000000) (δ := 559/100000000) (ψ := 504553/1000000) 58 32
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t32 : ((375863290803/2500000000000 : ℚ) : ℝ) ≤ stT58 32 := by
  have hc : ((425241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375863290803/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((425241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c33 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((333337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3077389/10000000) (δ := 43/12500000) (ψ := 504553/1000000) 58 32
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t33 : ((72522251339/1250000000000 : ℚ) : ℝ) ≤ stT58 33 := by
  have hc : ((333287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72522251339/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((333287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c34 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-983993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7406069/10000000) (δ := 439/100000000) (ψ := 504553/1000000) 58 32
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t34 : ((-843809984199/5000000000000 : ℚ) : ℝ) ≤ stT58 34 := by
  have hc : ((-984043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-843809984199/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-984043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c35 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-6863/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4098701/10000000) (δ := 3/800000) (ψ := 504553/1000000) 58 33
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t35 : ((-2902260553/250000000000 : ℚ) : ℝ) ≤ stT58 35 := by
  have hc : ((-1717/25000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2902260553/250000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-1717/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c36 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((62499/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3481/2500000) (δ := 87/25000000) (ψ := 504553/1000000) 58 33
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t36 : ((416639000011/2500000000000 : ℚ) : ℝ) ≤ stT58 36 := by
  have hc : ((499967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416639000011/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((499967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c37 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-6387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3958927/10000000) (δ := 127/25000000) (ψ := 504553/1000000) 58 33
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t37 : ((-263531597/125000000000 : ℚ) : ℝ) ≤ stT58 37 := by
  have hc : ((-1603/125000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263531597/125000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-1603/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c38 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-999937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7825823/10000000) (δ := 71/20000000) (ψ := 504553/1000000) 58 33
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t38 : ((-324438782241/2000000000000 : ℚ) : ℝ) ≤ stT58 38 := by
  have hc : ((-999987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324438782241/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-999987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c39 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-7541/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -823139/2000000) (δ := 317/100000000) (ψ := 504553/1000000) 58 34
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t39 : ((-3020818493/250000000000 : ℚ) : ℝ) ≤ stT58 39 := by
  have hc : ((-3773/50000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3020818493/250000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-3773/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c40 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((984227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -444613/10000000) (δ := 153/50000000) (ψ := 504553/1000000) 58 34
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t40 : ((778059826713/5000000000000 : ℚ) : ℝ) ≤ stT58 40 := by
  have hc : ((984177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((778059826713/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((984177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c41 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((155607/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391977/1250000) (δ := 193/50000000) (ψ := 504553/1000000) 58 34
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t41 : ((121489082967/2500000000000 : ℚ) : ℝ) ≤ stT58 41 := by
  have hc : ((77791/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121489082967/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((77791/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c42 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-882517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6629961/10000000) (δ := 477/100000000) (ψ := 504553/1000000) 58 34
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t42 : ((-680915444139/5000000000000 : ℚ) : ℝ) ≤ stT58 42 := by
  have hc : ((-882567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-680915444139/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-882567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c43 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-320437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35413/62500) (δ := 243/50000000) (ψ := 504553/1000000) 58 35
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t43 : ((-122175015883/1250000000000 : ℚ) : ℝ) ≤ stT58 43 := by
  have hc : ((-160231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122175015883/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-160231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c44 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((297697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11663/50000) (δ := 193/50000000) (ψ := 504553/1000000) 58 35
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t44 : ((14023662801/156250000000 : ℚ) : ℝ) ≤ stT58 44 := by
  have hc : ((37209/62500 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14023662801/156250000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((37209/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c45 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((233047/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231491/2500000) (δ := 517/100000000) (ψ := 504553/1000000) 58 35
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t45 : ((694774185059/5000000000000 : ℚ) : ℝ) ≤ stT58 45 := by
  have hc : ((466069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((694774185059/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((466069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c46 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-37149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2056453/5000000) (δ := 577/100000000) (ψ := 504553/1000000) 58 35
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t46 : ((-1370252227/125000000000 : ℚ) : ℝ) ≤ stT58 46 := by
  have hc : ((-18587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1370252227/125000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-18587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c47 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-484571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1446261/2000000) (δ := 293/50000000) (ψ := 504553/1000000) 58 35
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t47 : ((-3534279777/25000000000 : ℚ) : ℝ) ≤ stT58 47 := by
  have hc : ((-121149/125000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3534279777/25000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-121149/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c48 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-281813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2711957/5000000) (δ := 67/12500000) (ψ := 504553/1000000) 58 36
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t48 : ((-12712443909/156250000000 : ℚ) : ℝ) ≤ stT58 48 := by
  have hc : ((-140919/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12712443909/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-140919/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c49 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((35143/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2434117/10000000) (δ := 567/100000000) (ψ := 504553/1000000) 58 36
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t49 : ((401598450949/5000000000000 : ℚ) : ℝ) ≤ stT58 49 := by
  have hc : ((281119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((401598450949/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((281119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c50 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((24511/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123819/2500000) (δ := 67/12500000) (ψ := 504553/1000000) 58 36
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t50 : ((138648028307/1000000000000 : ℚ) : ℝ) ≤ stT58 50 := by
  have hc : ((98039/100000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138648028307/1000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((98039/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c51 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((111131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3366657/10000000) (δ := 47/12500000) (ψ := 504553/1000000) 58 36
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t51 : ((1944743871/62500000000 : ℚ) : ℝ) ≤ stT58 51 := by
  have hc : ((55553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1944743871/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((55553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c52 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-2452/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6182279/10000000) (δ := 119/25000000) (ψ := 504553/1000000) 58 36
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t52 : ((-108816964219/1000000000000 : ℚ) : ℝ) ≤ stT58 52 := by
  have hc : ((-78469/100000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108816964219/1000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-78469/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c53 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-1133/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -422731/625000) (δ := 101/20000000) (ψ := 504553/1000000) 58 37
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t53 : ((-12451051587/100000000000 : ℚ) : ℝ) ≤ stT58 53 := by
  have hc : ((-18129/20000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12451051587/100000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-18129/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c54 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-50517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4053337/10000000) (δ := 13/4000000) (ψ := 504553/1000000) 58 37
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t54 : ((-17203247369/2500000000000 : ℚ) : ℝ) ≤ stT58 54 := by
  have hc : ((-50567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17203247369/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-50567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c55 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((1061/1250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174089/1250000) (δ := 239/50000000) (ψ := 504553/1000000) 58 37
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t55 : ((915562921/8000000000 : ℚ) : ℝ) ≤ stT58 55 := by
  have hc : ((679/800 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((915562921/8000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((679/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c56 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((441639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 304993/2500000) (δ := 269/50000000) (ψ := 504553/1000000) 58 37
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t56 : ((147532859471/1250000000000 : ℚ) : ℝ) ≤ stT58 56 := by
  have hc : ((220807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147532859471/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((220807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c57 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((56203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378641/1000000) (δ := 189/50000000) (ψ := 504553/1000000) 58 37
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t57 : ((18594111349/2500000000000 : ℚ) : ℝ) ≤ stT58 57 := by
  have hc : ((56153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18594111349/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((56153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c58 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-814861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6308213/10000000) (δ := 21/4000000) (ψ := 504553/1000000) 58 37
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t58 : ((-214006222443/2000000000000 : ℚ) : ℝ) ≤ stT58 58 := by
  have hc : ((-814911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214006222443/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-814911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c59 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-116397/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6921057/10000000) (δ := 157/50000000) (ψ := 504553/1000000) 58 38
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t59 : ((-60617690857/500000000000 : ℚ) : ℝ) ≤ stT58 59 := by
  have hc : ((-465613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60617690857/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-465613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c60 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-8839/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179361/400000) (δ := 369/100000000) (ψ := 504553/1000000) 58 38
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t60 : ((-2282737359/80000000000 : ℚ) : ℝ) ≤ stT58 60 := by
  have hc : ((-8841/40000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2282737359/80000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-8841/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c61 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((167811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -521819/2500000) (δ := 389/100000000) (ψ := 504553/1000000) 58 38
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t61 : ((26855478731/312500000000 : ℚ) : ℝ) ≤ stT58 61 := by
  have hc : ((335597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26855478731/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((335597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c62 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((124269/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 270499/10000000) (δ := 489/100000000) (ψ := 504553/1000000) 58 38
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t62 : ((631255267051/5000000000000 : ℚ) : ℝ) ≤ stT58 62 := by
  have hc : ((497051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((631255267051/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((497051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c63 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((509477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2590549/10000000) (δ := 207/50000000) (ψ := 504553/1000000) 58 38
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t63 : ((641817398187/10000000000000 : ℚ) : ℝ) ≤ stT58 63 := by
  have hc : ((509427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((641817398187/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((509427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c64 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-46229/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 243703/500000) (δ := 469/100000000) (ψ := 504553/1000000) 58 38
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t64 : ((-231176434941/5000000000000 : ℚ) : ℝ) ≤ stT58 64 := by
  have hc : ((-184941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231176434941/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-184941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c65 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-957461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7122167/10000000) (δ := 389/100000000) (ψ := 504553/1000000) 58 38
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t65 : ((-296911713457/2500000000000 : ℚ) : ℝ) ≤ stT58 65 := by
  have hc : ((-957511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296911713457/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-957511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c66 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-414693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1593003/2500000) (δ := 323/100000000) (ψ := 504553/1000000) 58 39
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t66 : ((-51048260697/500000000000 : ℚ) : ℝ) ≤ stT58 66 := by
  have hc : ((-207359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51048260697/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-207359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c67 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-52807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26197/62500) (δ := 463/100000000) (ψ := 504553/1000000) 58 39
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t67 : ((-403403689/31250000000 : ℚ) : ℝ) ≤ stT58 67 := by
  have hc : ((-1651/15625 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403403689/31250000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-1651/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c68 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((684169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2043333/10000000) (δ := 563/100000000) (ψ := 504553/1000000) 58 39
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t68 : ((414808030341/5000000000000 : ℚ) : ℝ) ≤ stT58 68 := by
  have hc : ((684119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414808030341/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((684119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c69 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((62473/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73493/10000000) (δ := 563/100000000) (ψ := 504553/1000000) 58 39
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t69 : ((300819435111/2500000000000 : ℚ) : ℝ) ≤ stT58 69 := by
  have hc : ((499759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300819435111/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((499759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c70 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((649443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107993/500000) (δ := 343/100000000) (ψ := 504553/1000000) 58 39
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t70 : ((194043174151/2500000000000 : ℚ) : ℝ) ≤ stT58 70 := by
  have hc : ((649393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194043174151/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((649393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c71 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-115597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527079/1250000) (δ := 11/2500000) (ψ := 504553/1000000) 58 39
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t71 : ((-68623888977/5000000000000 : ℚ) : ℝ) ≤ stT58 71 := by
  have hc : ((-115647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68623888977/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-115647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c72 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-399929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6244637/10000000) (δ := 483/100000000) (ψ := 504553/1000000) 58 39
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t72 : ((-14729705889/156250000000 : ℚ) : ℝ) ≤ stT58 72 := by
  have hc : ((-199977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14729705889/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-199977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c73 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-493907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3731647/5000000) (δ := 333/100000000) (ψ := 504553/1000000) 58 40
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t73 : ((-36131496249/312500000000 : ℚ) : ℝ) ≤ stT58 73 := by
  have hc : ((-123483/125000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36131496249/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-123483/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c74 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-73177/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219619/400000) (δ := 53/10000000) (ψ := 504553/1000000) 58 40
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t74 : ((-340295379641/5000000000000 : ℚ) : ℝ) ≤ stT58 74 := by
  have hc : ((-292733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340295379641/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-292733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c75 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((4767/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3544137/10000000) (δ := 513/100000000) (ψ := 504553/1000000) 58 40
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t75 : ((880424109/50000000000 : ℚ) : ℝ) ≤ stT58 75 := by
  have hc : ((76247/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((880424109/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((76247/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c76 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((199107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1623579/10000000) (δ := 353/100000000) (ψ := 504553/1000000) 58 40
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t76 : ((228376920871/2500000000000 : ℚ) : ℝ) ≤ stT58 76 := by
  have hc : ((398189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((228376920871/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((398189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c77 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((994093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271873/10000000) (δ := 453/100000000) (ψ := 504553/1000000) 58 40
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t77 : ((226563274603/2000000000000 : ℚ) : ℝ) ≤ stT58 77 := by
  have hc : ((994043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226563274603/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((994043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c78 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((654597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2142867/10000000) (δ := 413/100000000) (ψ := 504553/1000000) 58 40
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t78 : ((741128513519/10000000000000 : ℚ) : ℝ) ≤ stT58 78 := by
  have hc : ((654547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((741128513519/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((654547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c79 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-25211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159601/400000) (δ := 293/100000000) (ψ := 504553/1000000) 58 40
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t79 : ((-888151499/312500000000 : ℚ) : ℝ) ≤ stT58 79 := by
  have hc : ((-25261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-888151499/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-25261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c80 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-685131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5813949/10000000) (δ := 373/100000000) (ψ := 504553/1000000) 58 40
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t80 : ((-383027827077/5000000000000 : ℚ) : ℝ) ≤ stT58 80 := by
  have hc : ((-685181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383027827077/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-685181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c81 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-995443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3807607/5000000) (δ := 31/10000000) (ψ := 504553/1000000) 58 40
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t81 : ((-138263027277/1250000000000 : ℚ) : ℝ) ≤ stT58 81 := by
  have hc : ((-995493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138263027277/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-995493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c82 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-163221/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3156793/5000000) (δ := 161/50000000) (ψ := 504553/1000000) 58 41
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t82 : ((-45064651249/500000000000 : ℚ) : ℝ) ≤ stT58 82 := by
  have hc : ((-163231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45064651249/500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-163231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c83 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-248953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1138997/2500000) (δ := 261/50000000) (ψ := 504553/1000000) 58 41
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t83 : ((-273316399929/10000000000000 : ℚ) : ℝ) ≤ stT58 83 := by
  have hc : ((-249003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273316399929/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-249003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c84 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((42867/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2819441/10000000) (δ := 301/50000000) (ψ := 504553/1000000) 58 41
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t84 : ((23383128359/500000000000 : ℚ) : ℝ) ≤ stT58 84 := by
  have hc : ((21431/50000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23383128359/500000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((21431/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c85 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((226041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275861/2500000) (δ := 341/100000000) (ψ := 504553/1000000) 58 41
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t85 : ((122581132291/1250000000000 : ℚ) : ℝ) ≤ stT58 85 := by
  have hc : ((452057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122581132291/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((452057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c86 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((60753/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 592481/10000000) (δ := 541/100000000) (ψ := 504553/1000000) 58 41
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t86 : ((524065843673/5000000000000 : ℚ) : ℝ) ≤ stT58 86 := by
  have hc : ((485999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524065843673/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((485999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c87 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((307851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2268801/10000000) (δ := 231/50000000) (ψ := 504553/1000000) 58 41
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t87 : ((10313248391/156250000000 : ℚ) : ℝ) ≤ stT58 87 := by
  have hc : ((153913/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10313248391/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((153913/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c88 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1962981/5000000) (δ := 241/50000000) (ψ := 504553/1000000) 58 41
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t88 : ((192946543/5000000000000 : ℚ) : ℝ) ≤ stT58 88 := by
  have hc : ((181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192946543/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c89 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-609129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5564397/10000000) (δ := 401/100000000) (ψ := 504553/1000000) 58 41
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t89 : ((-322864260821/5000000000000 : ℚ) : ℝ) ≤ stT58 89 := by
  have hc : ((-609179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322864260821/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-609179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c90 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-24109/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3592263/5000000) (δ := 421/100000000) (ψ := 504553/1000000) 58 41
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t90 : ((-101657783013/1000000000000 : ℚ) : ℝ) ≤ stT58 90 := by
  have hc : ((-96441/100000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101657783013/1000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-96441/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c91 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-931199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6921211/10000000) (δ := 79/12500000) (ψ := 504553/1000000) 58 42
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t91 : ((-195242871593/2000000000000 : ℚ) : ℝ) ≤ stT58 91 := by
  have hc : ((-931249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195242871593/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-931249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c92 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-133601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -333531/625000) (δ := 113/25000000) (ψ := 504553/1000000) 58 42
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t92 : ((-278603655071/5000000000000 : ℚ) : ℝ) ≤ stT58 92 := by
  have hc : ((-267227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278603655071/5000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-267227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c93 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((63189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3768913/10000000) (δ := 69/12500000) (ψ := 504553/1000000) 58 42
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t93 : ((65472049189/10000000000000 : ℚ) : ℝ) ≤ stT58 93 := by
  have hc : ((63139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65472049189/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((63139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c94 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((157889/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138631/625000) (δ := 123/25000000) (ψ := 504553/1000000) 58 42
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t94 : ((325674275013/5000000000000 : ℚ) : ℝ) ≤ stT58 94 := by
  have hc : ((315753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325674275013/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((315753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c95 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((481419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68369/1000000) (δ := 69/12500000) (ψ := 504553/1000000) 58 42
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t95 : ((123474913333/1250000000000 : ℚ) : ℝ) ≤ stT58 95 := by
  have hc : ((240697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123474913333/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((240697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c96 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((188957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104331/1250000) (δ := 133/25000000) (ψ := 504553/1000000) 58 42
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t96 : ((9642154357/100000000000 : ℚ) : ℝ) ≤ stT58 96 := by
  have hc : ((188947/200000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9642154357/100000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((188947/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c97 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((296949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 584313/2500000) (δ := 113/25000000) (ψ := 504553/1000000) 58 42
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t97 : ((37685074463/625000000000 : ℚ) : ℝ) ≤ stT58 97 := by
  have hc : ((74231/125000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37685074463/625000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((74231/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c98 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((41007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 764889/2000000) (δ := 59/12500000) (ψ := 504553/1000000) 58 42
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t98 : ((5171599433/1250000000000 : ℚ) : ℝ) ≤ stT58 98 := by
  have hc : ((40957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5171599433/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((40957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c99 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-520827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5296539/10000000) (δ := 39/12500000) (ψ := 504553/1000000) 58 42
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t99 : ((-261750589163/5000000000000 : ℚ) : ℝ) ≤ stT58 99 := by
  have hc : ((-520877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261750589163/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-520877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_c100 :
    |Real.cos (((58 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((504553/1000000 : ℚ) : ℝ))
      - ((-904727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6753837/10000000) (δ := 123/25000000) (ψ := 504553/1000000) 58 42
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st58_t100 : ((-904777/10000000 : ℚ) : ℝ) ≤ stT58 100 := by
  have hc : ((-904777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((58 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((504553/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st58_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-904777/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-904777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st58_p1 : ((875341/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT58 (i+1) := by
  rw [Finset.sum_range_one]
  exact st58_t1

theorem st58_p2 : ((1454426906843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT58 (i+1))
      = (∑ i ∈ Finset.range 1, stT58 (i+1)) + stT58 2 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 1
    simpa using h
  have hprev := st58_p1
  have hstep := st58_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p3 : ((1396548530661/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT58 (i+1))
      = (∑ i ∈ Finset.range 2, stT58 (i+1)) + stT58 3 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 2
    simpa using h
  have hprev := st58_p2
  have hstep := st58_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p4 : ((10129383036687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT58 (i+1))
      = (∑ i ∈ Finset.range 3, stT58 (i+1)) + stT58 4 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 3
    simpa using h
  have hprev := st58_p3
  have hstep := st58_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p5 : ((5433761167421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT58 (i+1))
      = (∑ i ∈ Finset.range 4, stT58 (i+1)) + stT58 5 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 4
    simpa using h
  have hprev := st58_p4
  have hstep := st58_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p6 : ((1729227925177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT58 (i+1))
      = (∑ i ∈ Finset.range 5, stT58 (i+1)) + stT58 6 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 5
    simpa using h
  have hprev := st58_p5
  have hstep := st58_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p7 : ((303442597119/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT58 (i+1))
      = (∑ i ∈ Finset.range 6, stT58 (i+1)) + stT58 7 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 6
    simpa using h
  have hprev := st58_p6
  have hstep := st58_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p8 : ((12362099235981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT58 (i+1))
      = (∑ i ∈ Finset.range 7, stT58 (i+1)) + stT58 8 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 7
    simpa using h
  have hprev := st58_p7
  have hstep := st58_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p9 : ((3336773951037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT58 (i+1))
      = (∑ i ∈ Finset.range 8, stT58 (i+1)) + stT58 9 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 8
    simpa using h
  have hprev := st58_p8
  have hstep := st58_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p10 : ((2957117430191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT58 (i+1))
      = (∑ i ∈ Finset.range 9, stT58 (i+1)) + stT58 10 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 9
    simpa using h
  have hprev := st58_p9
  have hstep := st58_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p11 : ((3524923510351/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT58 (i+1))
      = (∑ i ∈ Finset.range 10, stT58 (i+1)) + stT58 11 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 10
    simpa using h
  have hprev := st58_p10
  have hstep := st58_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p12 : ((9717087264677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT58 (i+1))
      = (∑ i ∈ Finset.range 11, stT58 (i+1)) + stT58 12 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 11
    simpa using h
  have hprev := st58_p11
  have hstep := st58_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p13 : ((3431404408363/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT58 (i+1))
      = (∑ i ∈ Finset.range 12, stT58 (i+1)) + stT58 13 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 12
    simpa using h
  have hprev := st58_p12
  have hstep := st58_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p14 : ((8321441730583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT58 (i+1))
      = (∑ i ∈ Finset.range 13, stT58 (i+1)) + stT58 14 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 13
    simpa using h
  have hprev := st58_p13
  have hstep := st58_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p15 : ((9443470435863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT58 (i+1))
      = (∑ i ∈ Finset.range 14, stT58 (i+1)) + stT58 15 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 14
    simpa using h
  have hprev := st58_p14
  have hstep := st58_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p16 : ((16395707375233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT58 (i+1))
      = (∑ i ∈ Finset.range 15, stT58 (i+1)) + stT58 16 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 15
    simpa using h
  have hprev := st58_p15
  have hstep := st58_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p17 : ((18569905634653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT58 (i+1))
      = (∑ i ∈ Finset.range 16, stT58 (i+1)) + stT58 17 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 16
    simpa using h
  have hprev := st58_p16
  have hstep := st58_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p18 : ((16668862876141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT58 (i+1))
      = (∑ i ∈ Finset.range 17, stT58 (i+1)) + stT58 18 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 17
    simpa using h
  have hprev := st58_p17
  have hstep := st58_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p19 : ((1852666433227/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT58 (i+1))
      = (∑ i ∈ Finset.range 18, stT58 (i+1)) + stT58 19 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 18
    simpa using h
  have hprev := st58_p18
  have hstep := st58_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p20 : ((8261619541529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT58 (i+1))
      = (∑ i ∈ Finset.range 19, stT58 (i+1)) + stT58 20 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 19
    simpa using h
  have hprev := st58_p19
  have hstep := st58_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p21 : ((583789727609/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT58 (i+1))
      = (∑ i ∈ Finset.range 20, stT58 (i+1)) + stT58 21 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 20
    simpa using h
  have hprev := st58_p20
  have hstep := st58_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p22 : ((2080147035047/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT58 (i+1))
      = (∑ i ∈ Finset.range 21, stT58 (i+1)) + stT58 22 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 21
    simpa using h
  have hprev := st58_p21
  have hstep := st58_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p23 : ((562632536519/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT58 (i+1))
      = (∑ i ∈ Finset.range 22, stT58 (i+1)) + stT58 23 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 22
    simpa using h
  have hprev := st58_p22
  have hstep := st58_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p24 : ((1792373662537/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT58 (i+1))
      = (∑ i ∈ Finset.range 23, stT58 (i+1)) + stT58 24 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 23
    simpa using h
  have hprev := st58_p23
  have hstep := st58_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p25 : ((1658317595509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT58 (i+1))
      = (∑ i ∈ Finset.range 24, stT58 (i+1)) + stT58 25 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 24
    simpa using h
  have hprev := st58_p24
  have hstep := st58_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p26 : ((741733078287/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT58 (i+1))
      = (∑ i ∈ Finset.range 25, stT58 (i+1)) + stT58 26 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 25
    simpa using h
  have hprev := st58_p25
  have hstep := st58_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p27 : ((3495261324547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT58 (i+1))
      = (∑ i ∈ Finset.range 26, stT58 (i+1)) + stT58 27 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 26
    simpa using h
  have hprev := st58_p26
  have hstep := st58_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p28 : ((8331668447563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT58 (i+1))
      = (∑ i ∈ Finset.range 27, stT58 (i+1)) + stT58 28 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 27
    simpa using h
  have hprev := st58_p27
  have hstep := st58_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p29 : ((3703966245547/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT58 (i+1))
      = (∑ i ∈ Finset.range 28, stT58 (i+1)) + stT58 29 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 28
    simpa using h
  have hprev := st58_p28
  have hstep := st58_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p30 : ((17783027483247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT58 (i+1))
      = (∑ i ∈ Finset.range 29, stT58 (i+1)) + stT58 30 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 29
    simpa using h
  have hprev := st58_p29
  have hstep := st58_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p31 : ((16464346675907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT58 (i+1))
      = (∑ i ∈ Finset.range 30, stT58 (i+1)) + stT58 31 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 30
    simpa using h
  have hprev := st58_p30
  have hstep := st58_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p32 : ((17967799839119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT58 (i+1))
      = (∑ i ∈ Finset.range 31, stT58 (i+1)) + stT58 32 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 31
    simpa using h
  have hprev := st58_p31
  have hstep := st58_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p33 : ((18547977849831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT58 (i+1))
      = (∑ i ∈ Finset.range 32, stT58 (i+1)) + stT58 33 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 32
    simpa using h
  have hprev := st58_p32
  have hstep := st58_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p34 : ((16860357881433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT58 (i+1))
      = (∑ i ∈ Finset.range 33, stT58 (i+1)) + stT58 34 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 33
    simpa using h
  have hprev := st58_p33
  have hstep := st58_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p35 : ((16744267459313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT58 (i+1))
      = (∑ i ∈ Finset.range 34, stT58 (i+1)) + stT58 35 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 34
    simpa using h
  have hprev := st58_p34
  have hstep := st58_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p36 : ((18410823459357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT58 (i+1))
      = (∑ i ∈ Finset.range 35, stT58 (i+1)) + stT58 36 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 35
    simpa using h
  have hprev := st58_p35
  have hstep := st58_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p37 : ((18389740931597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT58 (i+1))
      = (∑ i ∈ Finset.range 36, stT58 (i+1)) + stT58 37 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 36
    simpa using h
  have hprev := st58_p36
  have hstep := st58_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p38 : ((2095943377549/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT58 (i+1))
      = (∑ i ∈ Finset.range 37, stT58 (i+1)) + stT58 38 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 37
    simpa using h
  have hprev := st58_p37
  have hstep := st58_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p39 : ((520209821271/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT58 (i+1))
      = (∑ i ∈ Finset.range 38, stT58 (i+1)) + stT58 39 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 38
    simpa using h
  have hprev := st58_p38
  have hstep := st58_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p40 : ((9101416967049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT58 (i+1))
      = (∑ i ∈ Finset.range 39, stT58 (i+1)) + stT58 40 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 39
    simpa using h
  have hprev := st58_p39
  have hstep := st58_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p41 : ((9344395132983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT58 (i+1))
      = (∑ i ∈ Finset.range 40, stT58 (i+1)) + stT58 41 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 40
    simpa using h
  have hprev := st58_p40
  have hstep := st58_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p42 : ((2165869922211/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT58 (i+1))
      = (∑ i ∈ Finset.range 41, stT58 (i+1)) + stT58 42 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 41
    simpa using h
  have hprev := st58_p41
  have hstep := st58_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p43 : ((255461863291/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT58 (i+1))
      = (∑ i ∈ Finset.range 42, stT58 (i+1)) + stT58 43 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 42
    simpa using h
  have hprev := st58_p42
  have hstep := st58_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p44 : ((67371381523/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT58 (i+1))
      = (∑ i ∈ Finset.range 43, stT58 (i+1)) + stT58 44 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 43
    simpa using h
  have hprev := st58_p43
  have hstep := st58_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p45 : ((9318311020003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT58 (i+1))
      = (∑ i ∈ Finset.range 44, stT58 (i+1)) + stT58 45 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 44
    simpa using h
  have hprev := st58_p44
  have hstep := st58_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p46 : ((9263500930923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT58 (i+1))
      = (∑ i ∈ Finset.range 45, stT58 (i+1)) + stT58 46 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 45
    simpa using h
  have hprev := st58_p45
  have hstep := st58_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p47 : ((8556644975523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT58 (i+1))
      = (∑ i ∈ Finset.range 46, stT58 (i+1)) + stT58 47 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 46
    simpa using h
  have hprev := st58_p46
  have hstep := st58_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p48 : ((1629969354087/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT58 (i+1))
      = (∑ i ∈ Finset.range 47, stT58 (i+1)) + stT58 48 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 47
    simpa using h
  have hprev := st58_p47
  have hstep := st58_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p49 : ((1068930652673/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT58 (i+1))
      = (∑ i ∈ Finset.range 48, stT58 (i+1)) + stT58 49 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 48
    simpa using h
  have hprev := st58_p48
  have hstep := st58_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p50 : ((9244685362919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT58 (i+1))
      = (∑ i ∈ Finset.range 49, stT58 (i+1)) + stT58 50 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 49
    simpa using h
  have hprev := st58_p49
  have hstep := st58_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p51 : ((9400264872599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT58 (i+1))
      = (∑ i ∈ Finset.range 50, stT58 (i+1)) + stT58 51 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 50
    simpa using h
  have hprev := st58_p50
  have hstep := st58_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p52 : ((553511253219/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT58 (i+1))
      = (∑ i ∈ Finset.range 51, stT58 (i+1)) + stT58 52 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 51
    simpa using h
  have hprev := st58_p51
  have hstep := st58_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p53 : ((4116813736077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT58 (i+1))
      = (∑ i ∈ Finset.range 52, stT58 (i+1)) + stT58 53 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 52
    simpa using h
  have hprev := st58_p52
  have hstep := st58_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p54 : ((1024902622177/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT58 (i+1))
      = (∑ i ∈ Finset.range 53, stT58 (i+1)) + stT58 54 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 53
    simpa using h
  have hprev := st58_p53
  have hstep := st58_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p55 : ((8771447803041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT58 (i+1))
      = (∑ i ∈ Finset.range 54, stT58 (i+1)) + stT58 55 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 54
    simpa using h
  have hprev := st58_p54
  have hstep := st58_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p56 : ((374463169637/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT58 (i+1))
      = (∑ i ∈ Finset.range 55, stT58 (i+1)) + stT58 56 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 55
    simpa using h
  have hprev := st58_p55
  have hstep := st58_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p57 : ((9398767463623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT58 (i+1))
      = (∑ i ∈ Finset.range 56, stT58 (i+1)) + stT58 57 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 56
    simpa using h
  have hprev := st58_p56
  have hstep := st58_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p58 : ((17727503815031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT58 (i+1))
      = (∑ i ∈ Finset.range 57, stT58 (i+1)) + stT58 58 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 57
    simpa using h
  have hprev := st58_p57
  have hstep := st58_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p59 : ((16515149997891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT58 (i+1))
      = (∑ i ∈ Finset.range 58, stT58 (i+1)) + stT58 59 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 58
    simpa using h
  have hprev := st58_p58
  have hstep := st58_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p60 : ((1014362989251/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT58 (i+1))
      = (∑ i ∈ Finset.range 59, stT58 (i+1)) + stT58 60 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 59
    simpa using h
  have hprev := st58_p59
  have hstep := st58_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p61 : ((1068073946713/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT58 (i+1))
      = (∑ i ∈ Finset.range 60, stT58 (i+1)) + stT58 61 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 60
    simpa using h
  have hprev := st58_p60
  have hstep := st58_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p62 : ((1835169368151/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT58 (i+1))
      = (∑ i ∈ Finset.range 61, stT58 (i+1)) + stT58 62 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 61
    simpa using h
  have hprev := st58_p61
  have hstep := st58_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p63 : ((18993511079697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT58 (i+1))
      = (∑ i ∈ Finset.range 62, stT58 (i+1)) + stT58 63 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 62
    simpa using h
  have hprev := st58_p62
  have hstep := st58_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p64 : ((3706231641963/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT58 (i+1))
      = (∑ i ∈ Finset.range 63, stT58 (i+1)) + stT58 64 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 63
    simpa using h
  have hprev := st58_p63
  have hstep := st58_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p65 : ((17343511355987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT58 (i+1))
      = (∑ i ∈ Finset.range 64, stT58 (i+1)) + stT58 65 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 64
    simpa using h
  have hprev := st58_p64
  have hstep := st58_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p66 : ((16322546142047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT58 (i+1))
      = (∑ i ∈ Finset.range 65, stT58 (i+1)) + stT58 66 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 65
    simpa using h
  have hprev := st58_p65
  have hstep := st58_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p67 : ((16193456961567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT58 (i+1))
      = (∑ i ∈ Finset.range 66, stT58 (i+1)) + stT58 67 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 66
    simpa using h
  have hprev := st58_p66
  have hstep := st58_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p68 : ((17023073022249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT58 (i+1))
      = (∑ i ∈ Finset.range 67, stT58 (i+1)) + stT58 68 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 67
    simpa using h
  have hprev := st58_p67
  have hstep := st58_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p69 : ((18226350762693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT58 (i+1))
      = (∑ i ∈ Finset.range 68, stT58 (i+1)) + stT58 69 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 68
    simpa using h
  have hprev := st58_p68
  have hstep := st58_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p70 : ((19002523459297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT58 (i+1))
      = (∑ i ∈ Finset.range 69, stT58 (i+1)) + stT58 70 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 69
    simpa using h
  have hprev := st58_p69
  have hstep := st58_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p71 : ((18865275681343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT58 (i+1))
      = (∑ i ∈ Finset.range 70, stT58 (i+1)) + stT58 71 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 70
    simpa using h
  have hprev := st58_p70
  have hstep := st58_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p72 : ((17922574504447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT58 (i+1))
      = (∑ i ∈ Finset.range 71, stT58 (i+1)) + stT58 72 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 71
    simpa using h
  have hprev := st58_p71
  have hstep := st58_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p73 : ((16766366624479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT58 (i+1))
      = (∑ i ∈ Finset.range 72, stT58 (i+1)) + stT58 73 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 72
    simpa using h
  have hprev := st58_p72
  have hstep := st58_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p74 : ((16085775865197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT58 (i+1))
      = (∑ i ∈ Finset.range 73, stT58 (i+1)) + stT58 74 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 73
    simpa using h
  have hprev := st58_p73
  have hstep := st58_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p75 : ((16261860686997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT58 (i+1))
      = (∑ i ∈ Finset.range 74, stT58 (i+1)) + stT58 75 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 74
    simpa using h
  have hprev := st58_p74
  have hstep := st58_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p76 : ((17175368370481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT58 (i+1))
      = (∑ i ∈ Finset.range 75, stT58 (i+1)) + stT58 76 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 75
    simpa using h
  have hprev := st58_p75
  have hstep := st58_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p77 : ((2288523092937/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT58 (i+1))
      = (∑ i ∈ Finset.range 76, stT58 (i+1)) + stT58 77 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 76
    simpa using h
  have hprev := st58_p76
  have hstep := st58_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p78 : ((3809862651403/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT58 (i+1))
      = (∑ i ∈ Finset.range 77, stT58 (i+1)) + stT58 78 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 77
    simpa using h
  have hprev := st58_p77
  have hstep := st58_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p79 : ((19020892409047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT58 (i+1))
      = (∑ i ∈ Finset.range 78, stT58 (i+1)) + stT58 79 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 78
    simpa using h
  have hprev := st58_p78
  have hstep := st58_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p80 : ((18254836754893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT58 (i+1))
      = (∑ i ∈ Finset.range 79, stT58 (i+1)) + stT58 80 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 79
    simpa using h
  have hprev := st58_p79
  have hstep := st58_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p81 : ((17148732536677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT58 (i+1))
      = (∑ i ∈ Finset.range 80, stT58 (i+1)) + stT58 81 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 80
    simpa using h
  have hprev := st58_p80
  have hstep := st58_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p82 : ((16247439511697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT58 (i+1))
      = (∑ i ∈ Finset.range 81, stT58 (i+1)) + stT58 82 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 81
    simpa using h
  have hprev := st58_p81
  have hstep := st58_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p83 : ((1996765388971/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT58 (i+1))
      = (∑ i ∈ Finset.range 82, stT58 (i+1)) + stT58 83 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 82
    simpa using h
  have hprev := st58_p82
  have hstep := st58_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p84 : ((4110446419737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT58 (i+1))
      = (∑ i ∈ Finset.range 83, stT58 (i+1)) + stT58 84 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 83
    simpa using h
  have hprev := st58_p83
  have hstep := st58_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p85 : ((4355608684319/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT58 (i+1))
      = (∑ i ∈ Finset.range 84, stT58 (i+1)) + stT58 85 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 84
    simpa using h
  have hprev := st58_p84
  have hstep := st58_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p86 : ((9235283212311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT58 (i+1))
      = (∑ i ∈ Finset.range 85, stT58 (i+1)) + stT58 86 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 85
    simpa using h
  have hprev := st58_p85
  have hstep := st58_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p87 : ((9565307160823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT58 (i+1))
      = (∑ i ∈ Finset.range 86, stT58 (i+1)) + stT58 87 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 86
    simpa using h
  have hprev := st58_p86
  have hstep := st58_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p88 : ((4782750053683/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT58 (i+1))
      = (∑ i ∈ Finset.range 87, stT58 (i+1)) + stT58 88 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 87
    simpa using h
  have hprev := st58_p87
  have hstep := st58_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p89 : ((1848527169309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT58 (i+1))
      = (∑ i ∈ Finset.range 88, stT58 (i+1)) + stT58 89 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 88
    simpa using h
  have hprev := st58_p88
  have hstep := st58_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p90 : ((218358673287/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT58 (i+1))
      = (∑ i ∈ Finset.range 89, stT58 (i+1)) + stT58 90 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 89
    simpa using h
  have hprev := st58_p89
  have hstep := st58_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p91 : ((3298495900999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT58 (i+1))
      = (∑ i ∈ Finset.range 90, stT58 (i+1)) + stT58 91 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 90
    simpa using h
  have hprev := st58_p90
  have hstep := st58_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p92 : ((15935272194853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT58 (i+1))
      = (∑ i ∈ Finset.range 91, stT58 (i+1)) + stT58 92 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 91
    simpa using h
  have hprev := st58_p91
  have hstep := st58_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p93 : ((8000372122021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT58 (i+1))
      = (∑ i ∈ Finset.range 92, stT58 (i+1)) + stT58 93 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 92
    simpa using h
  have hprev := st58_p92
  have hstep := st58_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p94 : ((4163023198517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT58 (i+1))
      = (∑ i ∈ Finset.range 93, stT58 (i+1)) + stT58 94 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 93
    simpa using h
  have hprev := st58_p93
  have hstep := st58_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p95 : ((4409973025183/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT58 (i+1))
      = (∑ i ∈ Finset.range 94, stT58 (i+1)) + stT58 95 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 94
    simpa using h
  have hprev := st58_p94
  have hstep := st58_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p96 : ((1162756721027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT58 (i+1))
      = (∑ i ∈ Finset.range 95, stT58 (i+1)) + stT58 96 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 95
    simpa using h
  have hprev := st58_p95
  have hstep := st58_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p97 : ((120044179549/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT58 (i+1))
      = (∑ i ∈ Finset.range 96, stT58 (i+1)) + stT58 97 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 96
    simpa using h
  have hprev := st58_p96
  have hstep := st58_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p98 : ((2406055190413/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT58 (i+1))
      = (∑ i ∈ Finset.range 97, stT58 (i+1)) + stT58 98 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 97
    simpa using h
  have hprev := st58_p97
  have hstep := st58_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p99 : ((9362470172489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT58 (i+1))
      = (∑ i ∈ Finset.range 98, stT58 (i+1)) + stT58 99 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 98
    simpa using h
  have hprev := st58_p98
  have hstep := st58_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st58_p100 : ((8910081672489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT58 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT58 (i+1))
      = (∑ i ∈ Finset.range 99, stT58 (i+1)) + stT58 100 := by
    have h := Finset.sum_range_succ (fun i => stT58 (i+1)) 99
    simpa using h
  have hprev := st58_p99
  have hstep := st58_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 58`.** -/
theorem station_58_sign : hardyG (((58:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 58 100 (by norm_num) (by norm_num)
    ((504553/1000000 : ℚ) : ℝ)
  have hchain := st58_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT58 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((58:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((504553/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((58:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((58:ℕ)):ℝ)+1) * ((((58:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((605333/1160000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((8910081672489/5000000000000 : ℚ) : ℝ) - ((605333/1160000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((504553/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((58:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((504553/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((58:ℕ)):ℝ))).re
      - Real.sin ((504553/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((58:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((58:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((58:ℕ)):ℝ)
      = ((((58:ℕ)):ℝ) * (Real.log (((58:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((58:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_58
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
  have hθwin : |(((504553/1000000 : ℚ) : ℝ) + ((6:ℤ)) * (2*Real.pi) - Real.pi) - theta (((58:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((58:ℕ)):ℝ))
    (φ := ((504553/1000000 : ℚ) : ℝ) + ((6:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((504553/1000000 : ℚ) : ℝ) + ((6:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((504553/1000000 : ℚ)) : ℝ) - Real.pi) + ((6:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((504553/1000000 : ℚ)) : ℝ) - Real.pi) 6).1,
    (cos_sin_shift ((((504553/1000000 : ℚ)) : ℝ) - Real.pi) 6).2]
  exact cos_sin_flip ((504553/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_58_sign
end AxiomAudit
