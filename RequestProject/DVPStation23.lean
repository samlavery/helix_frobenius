import RequestProject.DVPSqrtTable

/-!
# Station `t = 23` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT23 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((23 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))

theorem st23_c1 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((993869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69243/2500000) (δ := 21/100000000) (ψ := -110789/1000000) 23 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t1 : ((993819/1000000 : ℚ) : ℝ) ≤ stT23 1 := by
  have hc : ((993819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((993819/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((993819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c2 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-235251/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3495477/5000000) (δ := 51/25000000) (ψ := -110789/1000000) 23 3
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t2 : ((-831782103209/1250000000000 : ℚ) : ℝ) ≤ stT23 2 := by
  have hc : ((-470527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-831782103209/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-470527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c3 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((969863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 307663/5000000) (δ := 51/25000000) (ψ := -110789/1000000) 23 4
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t3 : ((2799608647563/5000000000000 : ℚ) : ℝ) ≤ stT23 3 := by
  have hc : ((969813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2799608647563/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((969813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c4 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((104583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724541/5000000) (δ := 29/20000000) (ψ := -110789/1000000) 23 5
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t4 : ((418307/1000000 : ℚ) : ℝ) ≤ stT23 4 := by
  have hc : ((418307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418307/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((418307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c5 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((33649/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1428127/10000000) (δ := 197/100000000) (ψ := -110789/1000000) 23 6
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t5 : ((30094785269/80000000000 : ℚ) : ℝ) ≤ stT23 5 := by
  have hc : ((33647/40000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30094785269/80000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((33647/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c6 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-44337/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6652601/10000000) (δ := 157/100000000) (ψ := -110789/1000000) 23 7
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t6 : ((-362030509957/1000000000000 : ℚ) : ℝ) ≤ stT23 6 := by
  have hc : ((-88679/100000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362030509957/1000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-88679/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c7 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((316867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2211063/10000000) (δ := 63/50000000) (ψ := -110789/1000000) 23 7
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t7 : ((149693745531/625000000000 : ℚ) : ℝ) ≤ stT23 7 := by
  have hc : ((158421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149693745531/625000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((158421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c8 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-171639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1163769/2000000) (δ := 17/12500000) (ψ := -110789/1000000) 23 8
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t8 : ((-606879714401/2500000000000 : ℚ) : ℝ) ≤ stT23 8 := by
  have hc : ((-343303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-606879714401/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-343303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c9 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((464059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11921/125000) (δ := 197/100000000) (ψ := -110789/1000000) 23 8
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t9 : ((773389922661/2500000000000 : ℚ) : ℝ) ≤ stT23 9 := by
  have hc : ((232017/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((773389922661/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((232017/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c10 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-943807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7011909/10000000) (δ := 207/100000000) (ψ := -110789/1000000) 23 8
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t10 : ((-1492369113123/5000000000000 : ℚ) : ℝ) ≤ stT23 10 := by
  have hc : ((-943857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1492369113123/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-943857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c11 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((140343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3215719/10000000) (δ := 79/50000000) (ψ := -110789/1000000) 23 9
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t11 : ((211537312967/2500000000000 : ℚ) : ℝ) ≤ stT23 11 := by
  have hc : ((70159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211537312967/2500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((70159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c12 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((75511/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357487/2000000) (δ := 27/20000000) (ψ := -110789/1000000) 23 9
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t12 : ((108983510503/500000000000 : ℚ) : ℝ) ≤ stT23 12 := by
  have hc : ((37753/50000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108983510503/500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((37753/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c13 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-833361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6389891/10000000) (δ := 1/781250) (ψ := -110789/1000000) 23 9
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t13 : ((-2311466241911/10000000000000 : ℚ) : ℝ) ≤ stT23 13 := by
  have hc : ((-833411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2311466241911/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-833411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c14 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-5459/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158027/312500) (δ := 87/50000000) (ψ := -110789/1000000) 23 10
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t14 : ((-116731718001/1000000000000 : ℚ) : ℝ) ≤ stT23 14 := by
  have hc : ((-43677/100000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116731718001/1000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-43677/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c15 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((453243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -544887/5000000) (δ := 61/25000000) (ψ := -110789/1000000) 23 10
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t15 : ((146275429673/625000000000 : ℚ) : ℝ) ≤ stT23 15 := by
  have hc : ((226609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146275429673/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((226609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c16 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((124723/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2621191/10000000) (δ := 97/50000000) (ψ := -110789/1000000) 23 10
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t16 : ((249421/2000000 : ℚ) : ℝ) ≤ stT23 16 := by
  have hc : ((249421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249421/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((249421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c17 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-765647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6107107/10000000) (δ := 67/50000000) (ψ := -110789/1000000) 23 10
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t17 : ((-1857088578829/10000000000000 : ℚ) : ℝ) ≤ stT23 17 := by
  have hc : ((-765697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1857088578829/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-765697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c18 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-816257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6314247/10000000) (δ := 149/100000000) (ψ := -110789/1000000) 23 11
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t18 : ((-1924054374061/10000000000000 : ℚ) : ℝ) ≤ stT23 18 := by
  have hc : ((-816307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1924054374061/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-816307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c19 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((71163/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1602691/5000000) (δ := 189/100000000) (ψ := -110789/1000000) 23 11
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t19 : ((326460835257/5000000000000 : ℚ) : ℝ) ≤ stT23 19 := by
  have hc : ((142301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326460835257/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((142301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c20 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((994761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128009/5000000) (δ := 159/100000000) (ψ := -110789/1000000) 23 11
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t20 : ((2224240441637/10000000000000 : ℚ) : ℝ) ≤ stT23 20 := by
  have hc : ((994711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2224240441637/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((994711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c21 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((104713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2549417/10000000) (δ := 67/50000000) (ψ := -110789/1000000) 23 11
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t21 : ((114240291567/1000000000000 : ℚ) : ℝ) ≤ stT23 21 := by
  have hc : ((104703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114240291567/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((104703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c22 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-30997/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2612159/5000000) (δ := 139/100000000) (ψ := -110789/1000000) 23 11
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t22 : ((-66092514501/625000000000 : ℚ) : ℝ) ≤ stT23 22 := by
  have hc : ((-248001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66092514501/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-248001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c23 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-499783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3890147/5000000) (δ := 97/50000000) (ψ := -110789/1000000) 23 11
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t23 : ((-6513575951/31250000000 : ℚ) : ℝ) ≤ stT23 23 := by
  have hc : ((-15619/15625 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6513575951/31250000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-15619/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c24 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-291087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5480491/10000000) (δ := 143/100000000) (ψ := -110789/1000000) 23 12
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t24 : ((-37139377569/312500000000 : ℚ) : ℝ) ≤ stT23 24 := by
  have hc : ((-36389/62500 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37139377569/312500000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-36389/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c25 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((156099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3133227/10000000) (δ := 183/100000000) (ψ := -110789/1000000) 23 12
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t25 : ((78037/1250000 : ℚ) : ℝ) ≤ stT23 25 := by
  have hc : ((78037/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78037/1250000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((78037/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c26 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((234739/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219509/2500000) (δ := 153/100000000) (ψ := -110789/1000000) 23 12
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t26 : ((920672914933/5000000000000 : ℚ) : ℝ) ≤ stT23 26 := by
  have hc : ((469453/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((920672914933/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((469453/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c27 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((434699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1292033/10000000) (δ := 3/2000000) (ψ := -110789/1000000) 23 12
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t27 : ((836530113/5000000000 : ℚ) : ℝ) ≤ stT23 27 := by
  have hc : ((217337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((836530113/5000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((217337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c28 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((26977/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3383173/10000000) (δ := 193/100000000) (ψ := -110789/1000000) 23 12
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t28 : ((101939833413/2500000000000 : ℚ) : ℝ) ≤ stT23 28 := by
  have hc : ((107883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101939833413/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((107883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c29 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-278003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1350231/2500000) (δ := 143/100000000) (ψ := -110789/1000000) 23 12
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t29 : ((-64535650839/625000000000 : ℚ) : ℝ) ≤ stT23 29 := by
  have hc : ((-69507/125000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64535650839/625000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-69507/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c30 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-97977/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7350263/10000000) (δ := 1/500000) (ψ := -110789/1000000) 23 12
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t30 : ((-44722463161/250000000000 : ℚ) : ℝ) ≤ stT23 30 := by
  have hc : ((-48991/50000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44722463161/250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-48991/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c31 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-425561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3236143/5000000) (δ := 29/12500000) (ψ := -110789/1000000) 23 13
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t31 : ((-191093859411/1250000000000 : ℚ) : ℝ) ≤ stT23 31 := by
  have hc : ((-212793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191093859411/1250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-212793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c32 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-283937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290421/625000) (δ := 121/50000000) (ψ := -110789/1000000) 23 13
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t32 : ((-502022847029/10000000000000 : ℚ) : ℝ) ≤ stT23 32 := by
  have hc : ((-283987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502022847029/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-283987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c33 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((50953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -575473/2000000) (δ := 151/100000000) (ψ := -110789/1000000) 23 13
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t33 : ((44343439839/625000000000 : ℚ) : ℝ) ≤ stT23 33 := by
  have hc : ((203787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44343439839/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((203787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c34 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((894123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -58041/500000) (δ := 91/50000000) (ψ := -110789/1000000) 23 13
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t34 : ((306664356781/2000000000000 : ℚ) : ℝ) ≤ stT23 34 := by
  have hc : ((894073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306664356781/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((894073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c35 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((97959/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126491/2500000) (δ := 161/100000000) (ψ := -110789/1000000) 23 13
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t35 : ((20696553729/125000000000 : ℚ) : ℝ) ≤ stT23 35 := by
  have hc : ((48977/50000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20696553729/125000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((48977/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c36 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((329873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2125789/10000000) (δ := 71/50000000) (ψ := -110789/1000000) 23 13
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t36 : ((34359152923/312500000000 : ℚ) : ℝ) ≤ stT23 36 := by
  have hc : ((41231/62500 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34359152923/312500000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((41231/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c37 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((45091/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370123/1000000) (δ := 101/50000000) (ψ := -110789/1000000) 23 13
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t37 : ((37044004137/2500000000000 : ℚ) : ℝ) ≤ stT23 37 := by
  have hc : ((22533/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37044004137/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((22533/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c38 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-249769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2617327/5000000) (δ := 131/100000000) (ψ := -110789/1000000) 23 13
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t38 : ((-40521957371/500000000000 : ℚ) : ℝ) ≤ stT23 38 := by
  have hc : ((-124897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40521957371/500000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-124897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c39 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-900319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345649/2000000) (δ := 121/100000000) (ψ := -110789/1000000) 23 13
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t39 : ((-720872336529/5000000000000 : ℚ) : ℝ) ≤ stT23 39 := by
  have hc : ((-900369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-720872336529/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-900369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c40 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-991299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1504789/2000000) (δ := 121/100000000) (ψ := -110789/1000000) 23 14
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t40 : ((-1567460566511/10000000000000 : ℚ) : ℝ) ≤ stT23 40 := by
  have hc : ((-991349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1567460566511/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-991349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c41 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-382439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6104119/10000000) (δ := 43/25000000) (ψ := -110789/1000000) 23 14
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t41 : ((-583309143/4882812500 : ℚ) : ℝ) ≤ stT23 41 := by
  have hc : ((-11952/15625 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583309143/4882812500 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-11952/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c42 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-62269/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471851/1000000) (δ := 181/100000000) (ψ := -110789/1000000) 23 14
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t42 : ((-48049307243/1000000000000 : ℚ) : ℝ) ≤ stT23 42 := by
  have hc : ((-62279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48049307243/1000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-62279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c43 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((22271/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3365507/10000000) (δ := 211/100000000) (ψ := -110789/1000000) 23 14
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t43 : ((3395531601/100000000000 : ℚ) : ℝ) ≤ stT23 43 := by
  have hc : ((11133/50000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3395531601/100000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((11133/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c44 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((85511/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2043609/10000000) (δ := 141/100000000) (ψ := -110789/1000000) 23 14
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t44 : ((128903198891/1250000000000 : ℚ) : ℝ) ≤ stT23 44 := by
  have hc : ((342019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128903198891/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((342019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c45 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((29849/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37571/500000) (δ := 53/25000000) (ψ := -110789/1000000) 23 14
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t45 : ((711902454449/5000000000000 : ℚ) : ℝ) ≤ stT23 45 := by
  have hc : ((477559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((711902454449/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((477559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c46 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((15298/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 512367/10000000) (δ := 111/50000000) (ψ := -110789/1000000) 23 14
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t46 : ((721744319109/5000000000000 : ℚ) : ℝ) ≤ stT23 46 := by
  have hc : ((489511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((721744319109/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((489511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c47 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((765107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 874487/5000000) (δ := 221/100000000) (ψ := -110789/1000000) 23 14
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t47 : ((1115949627993/10000000000000 : ℚ) : ℝ) ≤ stT23 47 := by
  have hc : ((765057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1115949627993/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((765057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c48 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((23587/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591909/2000000) (δ := 201/100000000) (ψ := -110789/1000000) 23 14
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t48 : ((2178584037/40000000000 : ℚ) : ℝ) ≤ stT23 48 := by
  have hc : ((188671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2178584037/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((188671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c49 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-17431/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2072577/5000000) (δ := 29/12500000) (ψ := -110789/1000000) 23 14
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t49 : ((-6228931063/500000000000 : ℚ) : ℝ) ≤ stT23 49 := by
  have hc : ((-17441/200000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6228931063/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-17441/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c50 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-52433/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530681/1000000) (δ := 201/100000000) (ψ := -110789/1000000) 23 14
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t50 : ((-18539638433/250000000000 : ℚ) : ℝ) ≤ stT23 50 := by
  have hc : ((-26219/50000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18539638433/250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-26219/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c51 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-2642/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6445461/10000000) (δ := 141/100000000) (ψ := -110789/1000000) 23 14
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t51 : ((-118392358269/1000000000000 : ℚ) : ℝ) ≤ stT23 51 := by
  have hc : ((-84549/100000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118392358269/1000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-84549/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c52 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-248297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7562001/10000000) (δ := 171/100000000) (ψ := -110789/1000000) 23 14
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t52 : ((-688686894869/5000000000000 : ℚ) : ℝ) ≤ stT23 52 := by
  have hc : ((-496619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-688686894869/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-496619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c53 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-948821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7050691/10000000) (δ := 181/100000000) (ψ := -110789/1000000) 23 15
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t53 : ((-651687449413/5000000000000 : ℚ) : ℝ) ≤ stT23 53 := by
  have hc : ((-948871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-651687449413/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-948871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c54 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-365423/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2987947/5000000) (δ := 131/100000000) (ψ := -110789/1000000) 23 15
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t54 : ((-15540995967/156250000000 : ℚ) : ℝ) ≤ stT23 54 := by
  have hc : ((-45681/62500 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15540995967/156250000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-45681/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c55 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-387143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2460409/5000000) (δ := 53/25000000) (ψ := -110789/1000000) 23 15
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t55 : ((-1305227603/25000000000 : ℚ) : ℝ) ≤ stT23 55 := by
  have hc : ((-387193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1305227603/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-387193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c56 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((8447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1942377/5000000) (δ := 111/50000000) (ψ := -110789/1000000) 23 15
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t56 : ((2813592283/1250000000000 : ℚ) : ℝ) ≤ stT23 56 := by
  have hc : ((4211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2813592283/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((4211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c57 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((102849/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2867029/10000000) (δ := 71/50000000) (ψ := -110789/1000000) 23 15
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t57 : ((68105117509/1250000000000 : ℚ) : ℝ) ≤ stT23 57 := by
  have hc : ((205673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68105117509/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((205673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c58 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((366933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1867003/10000000) (δ := 191/100000000) (ψ := -110789/1000000) 23 15
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t58 : ((15055427691/156250000000 : ℚ) : ℝ) ≤ stT23 58 := by
  have hc : ((91727/125000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15055427691/156250000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((91727/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c59 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((469061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -884073/10000000) (δ := 61/50000000) (ψ := -110789/1000000) 23 15
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t59 : ((152658202251/1250000000000 : ℚ) : ℝ) ≤ stT23 59 := by
  have hc : ((117259/125000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152658202251/1250000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((117259/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c60 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((499729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2573/312500) (δ := 19/12500000) (ψ := -110789/1000000) 23 15
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t60 : ((40319679111/312500000000 : ℚ) : ℝ) ≤ stT23 60 := by
  have hc : ((62463/62500 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40319679111/312500000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((62463/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c61 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((915877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032771/10000000) (δ := 81/50000000) (ψ := -110789/1000000) 23 15
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t61 : ((73287224021/625000000000 : ℚ) : ℝ) ≤ stT23 61 := by
  have hc : ((915827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73287224021/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((915827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c62 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((352951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1967751/10000000) (δ := 53/25000000) (ψ := -110789/1000000) 23 15
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t62 : ((224108186463/2500000000000 : ℚ) : ℝ) ≤ stT23 62 := by
  have hc : ((176463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224108186463/2500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((176463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c63 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((20191/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 288777/1000000) (δ := 181/100000000) (ψ := -110789/1000000) 23 15
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t63 : ((50870215137/1000000000000 : ℚ) : ℝ) ≤ stT23 63 := by
  have hc : ((40377/100000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50870215137/1000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((40377/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c64 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((1069/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3793301/10000000) (δ := 101/50000000) (ψ := -110789/1000000) 23 15
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t64 : ((267/40000 : ℚ) : ℝ) ≤ stT23 64 := by
  have hc : ((267/5000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267/40000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((267/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c65 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-298499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4684791/10000000) (δ := 71/50000000) (ψ := -110789/1000000) 23 15
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t65 : ((-92576163763/2500000000000 : ℚ) : ℝ) ≤ stT23 65 := by
  have hc : ((-298549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92576163763/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-298549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_c66 :
    |Real.cos (((23 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ))
      - ((-304291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5562671/10000000) (δ := 141/100000000) (ψ := -110789/1000000) 23 15
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st23_t66 : ((-18729356457/250000000000 : ℚ) : ℝ) ≤ stT23 66 := by
  have hc : ((-76079/125000 : ℚ) : ℝ)
      ≤ Real.cos (((23 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-110789/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st23_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18729356457/250000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-76079/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st23_p1 : ((993819/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT23 (i+1) := by
  rw [Finset.sum_range_one]
  exact st23_t1

theorem st23_p2 : ((410491646791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT23 (i+1))
      = (∑ i ∈ Finset.range 1, stT23 (i+1)) + stT23 2 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 1
    simpa using h
  have hprev := st23_p1
  have hstep := st23_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p3 : ((4441575234727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT23 (i+1))
      = (∑ i ∈ Finset.range 2, stT23 (i+1)) + stT23 3 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 2
    simpa using h
  have hprev := st23_p2
  have hstep := st23_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p4 : ((6533110234727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT23 (i+1))
      = (∑ i ∈ Finset.range 3, stT23 (i+1)) + stT23 4 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 3
    simpa using h
  have hprev := st23_p3
  have hstep := st23_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p5 : ((16828068628079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT23 (i+1))
      = (∑ i ∈ Finset.range 4, stT23 (i+1)) + stT23 5 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 4
    simpa using h
  have hprev := st23_p4
  have hstep := st23_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p6 : ((13207763528509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT23 (i+1))
      = (∑ i ∈ Finset.range 5, stT23 (i+1)) + stT23 6 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 5
    simpa using h
  have hprev := st23_p5
  have hstep := st23_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p7 : ((3120572691401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT23 (i+1))
      = (∑ i ∈ Finset.range 6, stT23 (i+1)) + stT23 7 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 6
    simpa using h
  have hprev := st23_p6
  have hstep := st23_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p8 : ((13175344599401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT23 (i+1))
      = (∑ i ∈ Finset.range 7, stT23 (i+1)) + stT23 8 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 7
    simpa using h
  have hprev := st23_p7
  have hstep := st23_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p9 : ((3253780858009/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT23 (i+1))
      = (∑ i ∈ Finset.range 8, stT23 (i+1)) + stT23 9 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 8
    simpa using h
  have hprev := st23_p8
  have hstep := st23_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p10 : ((13284166063799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT23 (i+1))
      = (∑ i ∈ Finset.range 9, stT23 (i+1)) + stT23 10 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 9
    simpa using h
  have hprev := st23_p9
  have hstep := st23_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p11 : ((14130315315667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT23 (i+1))
      = (∑ i ∈ Finset.range 10, stT23 (i+1)) + stT23 11 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 10
    simpa using h
  have hprev := st23_p10
  have hstep := st23_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p12 : ((16309985525727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT23 (i+1))
      = (∑ i ∈ Finset.range 11, stT23 (i+1)) + stT23 12 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 11
    simpa using h
  have hprev := st23_p11
  have hstep := st23_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p13 : ((1749814910477/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT23 (i+1))
      = (∑ i ∈ Finset.range 12, stT23 (i+1)) + stT23 13 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 12
    simpa using h
  have hprev := st23_p12
  have hstep := st23_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p14 : ((6415601051903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT23 (i+1))
      = (∑ i ∈ Finset.range 13, stT23 (i+1)) + stT23 14 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 13
    simpa using h
  have hprev := st23_p13
  have hstep := st23_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p15 : ((7585804489287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT23 (i+1))
      = (∑ i ∈ Finset.range 14, stT23 (i+1)) + stT23 15 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 14
    simpa using h
  have hprev := st23_p14
  have hstep := st23_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p16 : ((8209356989287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT23 (i+1))
      = (∑ i ∈ Finset.range 15, stT23 (i+1)) + stT23 16 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 15
    simpa using h
  have hprev := st23_p15
  have hstep := st23_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p17 : ((2912325079949/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT23 (i+1))
      = (∑ i ∈ Finset.range 16, stT23 (i+1)) + stT23 17 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 16
    simpa using h
  have hprev := st23_p16
  have hstep := st23_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p18 : ((3159392756421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT23 (i+1))
      = (∑ i ∈ Finset.range 17, stT23 (i+1)) + stT23 18 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 17
    simpa using h
  have hprev := st23_p17
  have hstep := st23_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p19 : ((6645246348099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT23 (i+1))
      = (∑ i ∈ Finset.range 18, stT23 (i+1)) + stT23 19 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 18
    simpa using h
  have hprev := st23_p18
  have hstep := st23_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p20 : ((3102946627567/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT23 (i+1))
      = (∑ i ∈ Finset.range 19, stT23 (i+1)) + stT23 20 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 19
    simpa using h
  have hprev := st23_p19
  have hstep := st23_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p21 : ((3331427210701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT23 (i+1))
      = (∑ i ∈ Finset.range 20, stT23 (i+1)) + stT23 21 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 20
    simpa using h
  have hprev := st23_p20
  have hstep := st23_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p22 : ((15599655821489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT23 (i+1))
      = (∑ i ∈ Finset.range 21, stT23 (i+1)) + stT23 22 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 21
    simpa using h
  have hprev := st23_p21
  have hstep := st23_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p23 : ((13515311517169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT23 (i+1))
      = (∑ i ∈ Finset.range 22, stT23 (i+1)) + stT23 23 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 22
    simpa using h
  have hprev := st23_p22
  have hstep := st23_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p24 : ((12326851434961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT23 (i+1))
      = (∑ i ∈ Finset.range 23, stT23 (i+1)) + stT23 24 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 23
    simpa using h
  have hprev := st23_p23
  have hstep := st23_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p25 : ((12951147434961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT23 (i+1))
      = (∑ i ∈ Finset.range 24, stT23 (i+1)) + stT23 25 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 24
    simpa using h
  have hprev := st23_p24
  have hstep := st23_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p26 : ((14792493264827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT23 (i+1))
      = (∑ i ∈ Finset.range 25, stT23 (i+1)) + stT23 26 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 25
    simpa using h
  have hprev := st23_p25
  have hstep := st23_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p27 : ((16465553490827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT23 (i+1))
      = (∑ i ∈ Finset.range 26, stT23 (i+1)) + stT23 27 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 26
    simpa using h
  have hprev := st23_p26
  have hstep := st23_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p28 : ((16873312824479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT23 (i+1))
      = (∑ i ∈ Finset.range 27, stT23 (i+1)) + stT23 28 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 27
    simpa using h
  have hprev := st23_p27
  have hstep := st23_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p29 : ((3168148482211/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT23 (i+1))
      = (∑ i ∈ Finset.range 28, stT23 (i+1)) + stT23 29 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 28
    simpa using h
  have hprev := st23_p28
  have hstep := st23_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p30 : ((2810368776923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT23 (i+1))
      = (∑ i ∈ Finset.range 29, stT23 (i+1)) + stT23 30 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 29
    simpa using h
  have hprev := st23_p29
  have hstep := st23_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p31 : ((12523093009327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT23 (i+1))
      = (∑ i ∈ Finset.range 30, stT23 (i+1)) + stT23 31 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 30
    simpa using h
  have hprev := st23_p30
  have hstep := st23_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p32 : ((6010535081149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT23 (i+1))
      = (∑ i ∈ Finset.range 31, stT23 (i+1)) + stT23 32 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 31
    simpa using h
  have hprev := st23_p31
  have hstep := st23_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p33 : ((6365282599861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT23 (i+1))
      = (∑ i ∈ Finset.range 32, stT23 (i+1)) + stT23 33 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 32
    simpa using h
  have hprev := st23_p32
  have hstep := st23_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p34 : ((14263886983627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT23 (i+1))
      = (∑ i ∈ Finset.range 33, stT23 (i+1)) + stT23 34 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 33
    simpa using h
  have hprev := st23_p33
  have hstep := st23_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p35 : ((15919611281947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT23 (i+1))
      = (∑ i ∈ Finset.range 34, stT23 (i+1)) + stT23 35 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 34
    simpa using h
  have hprev := st23_p34
  have hstep := st23_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p36 : ((17019104175483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT23 (i+1))
      = (∑ i ∈ Finset.range 35, stT23 (i+1)) + stT23 36 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 35
    simpa using h
  have hprev := st23_p35
  have hstep := st23_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p37 : ((17167280192031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT23 (i+1))
      = (∑ i ∈ Finset.range 36, stT23 (i+1)) + stT23 37 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 36
    simpa using h
  have hprev := st23_p36
  have hstep := st23_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p38 : ((16356841044611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT23 (i+1))
      = (∑ i ∈ Finset.range 37, stT23 (i+1)) + stT23 38 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 37
    simpa using h
  have hprev := st23_p37
  have hstep := st23_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p39 : ((14915096371553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT23 (i+1))
      = (∑ i ∈ Finset.range 38, stT23 (i+1)) + stT23 39 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 38
    simpa using h
  have hprev := st23_p38
  have hstep := st23_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p40 : ((6673817902521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT23 (i+1))
      = (∑ i ∈ Finset.range 39, stT23 (i+1)) + stT23 40 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 39
    simpa using h
  have hprev := st23_p39
  have hstep := st23_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p41 : ((6076509340089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT23 (i+1))
      = (∑ i ∈ Finset.range 40, stT23 (i+1)) + stT23 41 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 40
    simpa using h
  have hprev := st23_p40
  have hstep := st23_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p42 : ((2918131401937/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT23 (i+1))
      = (∑ i ∈ Finset.range 41, stT23 (i+1)) + stT23 42 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 41
    simpa using h
  have hprev := st23_p41
  have hstep := st23_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p43 : ((1501509845981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT23 (i+1))
      = (∑ i ∈ Finset.range 42, stT23 (i+1)) + stT23 43 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 42
    simpa using h
  have hprev := st23_p42
  have hstep := st23_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p44 : ((203801630609/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT23 (i+1))
      = (∑ i ∈ Finset.range 43, stT23 (i+1)) + stT23 44 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 43
    simpa using h
  have hprev := st23_p43
  have hstep := st23_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p45 : ((7233554633937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT23 (i+1))
      = (∑ i ∈ Finset.range 44, stT23 (i+1)) + stT23 45 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 44
    simpa using h
  have hprev := st23_p44
  have hstep := st23_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p46 : ((3977649476523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT23 (i+1))
      = (∑ i ∈ Finset.range 45, stT23 (i+1)) + stT23 46 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 45
    simpa using h
  have hprev := st23_p45
  have hstep := st23_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p47 : ((3405309506817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT23 (i+1))
      = (∑ i ∈ Finset.range 46, stT23 (i+1)) + stT23 47 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 46
    simpa using h
  have hprev := st23_p46
  have hstep := st23_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p48 : ((3514238708667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT23 (i+1))
      = (∑ i ∈ Finset.range 47, stT23 (i+1)) + stT23 48 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 47
    simpa using h
  have hprev := st23_p47
  have hstep := st23_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p49 : ((697864596883/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT23 (i+1))
      = (∑ i ∈ Finset.range 48, stT23 (i+1)) + stT23 49 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 48
    simpa using h
  have hprev := st23_p48
  have hstep := st23_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p50 : ((3341005876951/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT23 (i+1))
      = (∑ i ∈ Finset.range 49, stT23 (i+1)) + stT23 50 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 49
    simpa using h
  have hprev := st23_p49
  have hstep := st23_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p51 : ((3104221160413/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT23 (i+1))
      = (∑ i ∈ Finset.range 50, stT23 (i+1)) + stT23 51 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 50
    simpa using h
  have hprev := st23_p50
  have hstep := st23_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p52 : ((14143732012327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT23 (i+1))
      = (∑ i ∈ Finset.range 51, stT23 (i+1)) + stT23 52 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 51
    simpa using h
  have hprev := st23_p51
  have hstep := st23_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p53 : ((12840357113501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT23 (i+1))
      = (∑ i ∈ Finset.range 52, stT23 (i+1)) + stT23 53 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 52
    simpa using h
  have hprev := st23_p52
  have hstep := st23_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p54 : ((11845733371613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT23 (i+1))
      = (∑ i ∈ Finset.range 53, stT23 (i+1)) + stT23 54 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 53
    simpa using h
  have hprev := st23_p53
  have hstep := st23_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p55 : ((11323642330413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT23 (i+1))
      = (∑ i ∈ Finset.range 54, stT23 (i+1)) + stT23 55 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 54
    simpa using h
  have hprev := st23_p54
  have hstep := st23_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p56 : ((11346151068677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT23 (i+1))
      = (∑ i ∈ Finset.range 55, stT23 (i+1)) + stT23 56 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 55
    simpa using h
  have hprev := st23_p55
  have hstep := st23_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p57 : ((11890992008749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT23 (i+1))
      = (∑ i ∈ Finset.range 56, stT23 (i+1)) + stT23 57 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 56
    simpa using h
  have hprev := st23_p56
  have hstep := st23_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p58 : ((12854539380973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT23 (i+1))
      = (∑ i ∈ Finset.range 57, stT23 (i+1)) + stT23 58 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 57
    simpa using h
  have hprev := st23_p57
  have hstep := st23_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p59 : ((14075804998981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT23 (i+1))
      = (∑ i ∈ Finset.range 58, stT23 (i+1)) + stT23 59 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 58
    simpa using h
  have hprev := st23_p58
  have hstep := st23_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p60 : ((15366034730533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT23 (i+1))
      = (∑ i ∈ Finset.range 59, stT23 (i+1)) + stT23 60 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 59
    simpa using h
  have hprev := st23_p59
  have hstep := st23_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p61 : ((16538630314869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT23 (i+1))
      = (∑ i ∈ Finset.range 60, stT23 (i+1)) + stT23 61 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 60
    simpa using h
  have hprev := st23_p60
  have hstep := st23_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p62 : ((17435063060721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT23 (i+1))
      = (∑ i ∈ Finset.range 61, stT23 (i+1)) + stT23 62 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 61
    simpa using h
  have hprev := st23_p61
  have hstep := st23_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p63 : ((17943765212091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT23 (i+1))
      = (∑ i ∈ Finset.range 62, stT23 (i+1)) + stT23 63 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 62
    simpa using h
  have hprev := st23_p62
  have hstep := st23_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p64 : ((18010515212091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT23 (i+1))
      = (∑ i ∈ Finset.range 63, stT23 (i+1)) + stT23 64 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 63
    simpa using h
  have hprev := st23_p63
  have hstep := st23_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p65 : ((17640210557039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT23 (i+1))
      = (∑ i ∈ Finset.range 64, stT23 (i+1)) + stT23 65 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 64
    simpa using h
  have hprev := st23_p64
  have hstep := st23_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st23_p66 : ((16891036298759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT23 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT23 (i+1))
      = (∑ i ∈ Finset.range 65, stT23 (i+1)) + stT23 66 := by
    have h := Finset.sum_range_succ (fun i => stT23 (i+1)) 65
    simpa using h
  have hprev := st23_p65
  have hstep := st23_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 23`.** -/
theorem station_23_sign : hardyG (((23:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 23 66 (by norm_num) (by norm_num)
    ((-110789/1000000 : ℚ) : ℝ)
  have hchain := st23_p66
  have hbridge : (∑ i ∈ Finset.range 66, stT23 (i+1))
      = ∑ i ∈ Finset.range 66,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((23:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-110789/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_66
  have hsh := rpow_half_shifts (N := 66) (by norm_num)
  have hcost : ((66:ℕ):ℝ) ^ ((1/2:ℝ)) / (((23:ℕ)):ℝ)
      + ((66:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((23:ℕ)):ℝ)+1) * ((((23:ℕ)):ℝ)+2) / 8
        * (((66:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((66:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2271530541/4452800000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((16891036298759/10000000000000 : ℚ) : ℝ) - ((2271530541/4452800000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-110789/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((23:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-110789/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((23:ℕ)):ℝ))).re
      - Real.sin ((-110789/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((23:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (((23:ℕ)):ℝ)) (T := (30:ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((23:ℕ)):ℝ)
      = ((((23:ℕ)):ℝ) * (Real.log (((23:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((23:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_23
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
  have hθwin : |(((-110789/1000000 : ℚ) : ℝ) + ((1:ℤ)) * (2*Real.pi) - Real.pi) - theta (((23:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((23:ℕ)):ℝ))
    (φ := ((-110789/1000000 : ℚ) : ℝ) + ((1:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-110789/1000000 : ℚ) : ℝ) + ((1:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-110789/1000000 : ℚ)) : ℝ) - Real.pi) + ((1:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-110789/1000000 : ℚ)) : ℝ) - Real.pi) 1).1,
    (cos_sin_shift ((((-110789/1000000 : ℚ)) : ℝ) - Real.pi) 1).2]
  exact cos_sin_flip ((-110789/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_23_sign
end AxiomAudit
