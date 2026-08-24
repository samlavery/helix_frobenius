import RequestProject.DVPSqrtTable

/-!
# Station `t = 35` of the Hardy ladder (sign +)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT35 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((35 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-100683/250000 : ℚ) : ℝ))

theorem st35_c1 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((459997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 100683/1000000) (δ := 1/100000000) (ψ := -100683/250000) 35 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t1 : ((114993/125000 : ℚ) : ℝ) ≤ stT35 1 := by
  have hc : ((114993/125000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114993/125000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((114993/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c2 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((891633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -234929/2000000) (δ := 137/50000000) (ψ := -100683/250000) 35 4
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t2 : ((6304443129061/10000000000000 : ℚ) : ℝ) ≤ stT35 2 := by
  have hc : ((891583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6304443129061/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((891583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c3 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((12621/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1443813/5000000) (δ := 163/50000000) (ψ := -100683/250000) 35 6
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t3 : ((582866781161/2500000000000 : ℚ) : ℝ) ≤ stT35 3 := by
  have hc : ((201911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((582866781161/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((201911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c4 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((226369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83903/250000) (δ := 197/100000000) (ψ := -100683/250000) 35 8
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t4 : ((226319/2000000 : ℚ) : ℝ) ≤ stT35 4 := by
  have hc : ((226319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226319/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((226319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c5 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((122881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230489/5000000) (δ := 61/20000000) (ψ := -100683/250000) 35 9
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t5 : ((439609976073/1000000000000 : ℚ) : ℝ) ≤ stT35 5 := by
  have hc : ((491499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439609976073/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((491499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c6 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((960373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 706151/10000000) (δ := 249/100000000) (ψ := -100683/250000) 35 10
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t6 : ((1960250680843/5000000000000 : ℚ) : ℝ) ≤ stT35 6 := by
  have hc : ((960323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1960250680843/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((960323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c7 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((164449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378407/2500000) (δ := 23/12500000) (ψ := -100683/250000) 35 11
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t7 : ((155380219929/500000000000 : ℚ) : ℝ) ≤ stT35 7 := by
  have hc : ((164439/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155380219929/500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((164439/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c8 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-37537/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2768797/5000000) (δ := 193/100000000) (ψ := -100683/250000) 35 12
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t8 : ((-530897553207/2500000000000 : ℚ) : ℝ) ≤ stT35 8 := by
  have hc : ((-300321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530897553207/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-300321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c9 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-330253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4768421/10000000) (δ := 13/5000000) (ψ := -100683/250000) 35 12
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t9 : ((-550505110101/5000000000000 : ℚ) : ℝ) ≤ stT35 9 := by
  have hc : ((-330303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550505110101/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-330303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c10 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((772391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1720497/10000000) (δ := 321/100000000) (ψ := -100683/250000) 35 13
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t10 : ((2442356180457/10000000000000 : ℚ) : ℝ) ≤ stT35 10 := by
  have hc : ((772341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2442356180457/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((772341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c11 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-440237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 827393/1250000) (δ := 261/100000000) (ψ := -100683/250000) 35 13
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t11 : ((-331860029967/1250000000000 : ℚ) : ℝ) ≤ stT35 11 := by
  have hc : ((-220131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331860029967/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-220131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c12 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((830869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368831/2500000) (δ := 181/100000000) (ψ := -100683/250000) 35 14
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t12 : ((2398367579069/10000000000000 : ℚ) : ℝ) ≤ stT35 12 := by
  have hc : ((830819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2398367579069/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((830819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c13 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-149413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5528413/10000000) (δ := 101/50000000) (ψ := -100683/250000) 35 14
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t13 : ((-828863547351/5000000000000 : ℚ) : ℝ) ≤ stT35 13 := by
  have hc : ((-298851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-828863547351/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-298851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c14 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((46311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3695103/10000000) (δ := 261/100000000) (ψ := -100683/250000) 35 15
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t14 : ((15463064879/625000000000 : ℚ) : ℝ) ≤ stT35 14 := by
  have hc : ((23143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15463064879/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((23143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c15 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((296221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1170887/5000000) (δ := 331/100000000) (ψ := -100683/250000) 35 15
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t15 : ((47798407353/312500000000 : ℚ) : ℝ) ≤ stT35 15 := by
  have hc : ((74049/125000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47798407353/312500000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((74049/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c16 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-62409/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7719069/10000000) (δ := 27/10000000) (ψ := -100683/250000) 35 16
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t16 : ((-1248242999297/5000000000000 : ℚ) : ℝ) ≤ stT35 16 := by
  have hc : ((-499297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1248242999297/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-499297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c17 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((568787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482883/2000000) (δ := 21/10000000) (ψ := -100683/250000) 35 16
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t17 : ((344847423843/2500000000000 : ℚ) : ℝ) ≤ stT35 17 := by
  have hc : ((568737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344847423843/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((568737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c18 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((127679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2586947/10000000) (δ := 223/100000000) (ψ := -100683/250000) 35 16
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t18 : ((300912749163/2500000000000 : ℚ) : ℝ) ≤ stT35 18 := by
  have hc : ((255333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300912749163/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((255333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c19 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-977091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1829457/2500000) (δ := 263/100000000) (ψ := -100683/250000) 35 16
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t19 : ((-1120857921139/5000000000000 : ℚ) : ℝ) ≤ stT35 19 := by
  have hc : ((-977141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1120857921139/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-977141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c20 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((10007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -975493/2500000) (δ := 61/25000000) (ψ := -100683/250000) 35 17
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t20 : ((22264519119/10000000000000 : ℚ) : ℝ) ≤ stT35 20 := by
  have hc : ((9957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22264519119/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((9957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c21 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((494617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5737/156250) (δ := 209/100000000) (ψ := -100683/250000) 35 17
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t21 : ((526995987/2441406250 : ℚ) : ℝ) ≤ stT35 21 := by
  have hc : ((15456/15625 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((526995987/2441406250 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((15456/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c22 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-101427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4437669/10000000) (δ := 23/12500000) (ψ := -100683/250000) 35 17
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t22 : ((-6759264863/156250000000 : ℚ) : ℝ) ≤ stT35 22 := by
  have hc : ((-25363/125000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6759264863/156250000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-25363/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c23 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-982139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1476153/2000000) (δ := 299/100000000) (ψ := -100683/250000) 35 18
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t23 : ((-409601296481/2000000000000 : ℚ) : ℝ) ≤ stT35 23 := by
  have hc : ((-982189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-409601296481/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-982189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c24 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((53933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3656799/10000000) (δ := 259/100000000) (ψ := -100683/250000) 35 18
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t24 : ((27509804957/1250000000000 : ℚ) : ℝ) ≤ stT35 24 := by
  have hc : ((13477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27509804957/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((13477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c25 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((15616/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42437/5000000) (δ := 259/100000000) (ψ := -100683/250000) 35 18
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t25 : ((499687/2500000 : ℚ) : ℝ) ≤ stT35 25 := by
  have hc : ((499687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499687/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((499687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c26 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((45989/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1673469/5000000) (δ := 229/100000000) (ψ := -100683/250000) 35 18
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t26 : ((90172221619/2000000000000 : ℚ) : ℝ) ≤ stT35 26 := by
  have hc : ((45979/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90172221619/2000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((45979/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c27 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-886113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6649217/10000000) (δ := 117/50000000) (ψ := -100683/250000) 35 18
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t27 : ((-1705421579663/10000000000000 : ℚ) : ℝ) ≤ stT35 27 := by
  have hc : ((-886163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1705421579663/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-886163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c28 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-351581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5876577/10000000) (δ := 149/50000000) (ψ := -100683/250000) 35 19
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t28 : ((-332236552869/2500000000000 : ℚ) : ℝ) ≤ stT35 28 := by
  have hc : ((-175803/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332236552869/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-175803/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c29 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((43349/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2806087/10000000) (δ := 31/12500000) (ψ := -100683/250000) 35 19
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t29 : ((5030485677/62500000000 : ℚ) : ℝ) ≤ stT35 29 := by
  have hc : ((2709/6250 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5030485677/62500000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((2709/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c30 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((199589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160299/10000000) (δ := 59/20000000) (ψ := -100683/250000) 35 19
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t30 : ((364379563039/2000000000000 : ℚ) : ℝ) ≤ stT35 30 := by
  have hc : ((199579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364379563039/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((199579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c31 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((351369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94669/312500) (δ := 87/25000000) (ψ := -100683/250000) 35 19
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t31 : ((630987543907/10000000000000 : ℚ) : ℝ) ≤ stT35 31 := by
  have hc : ((351319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630987543907/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((351319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c32 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-341613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5807419/10000000) (δ := 179/50000000) (ψ := -100683/250000) 35 19
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t32 : ((-301968191173/2500000000000 : ℚ) : ℝ) ≤ stT35 32 := by
  have hc : ((-170819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301968191173/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-170819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c33 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-241701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -901003/1250000) (δ := 103/50000000) (ψ := -100683/250000) 35 20
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t33 : ((-841538602779/5000000000000 : ℚ) : ℝ) ≤ stT35 33 := by
  have hc : ((-483427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-841538602779/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-483427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c34 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-132189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4595889/10000000) (δ := 247/100000000) (ψ := -100683/250000) 35 20
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t34 : ((-56686289751/1250000000000 : ℚ) : ℝ) ≤ stT35 34 := by
  have hc : ((-66107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56686289751/1250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-66107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c35 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((169861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51487/250000) (δ := 27/12500000) (ψ := -100683/250000) 35 20
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t35 : ((143548139169/1250000000000 : ℚ) : ℝ) ≤ stT35 35 := by
  have hc : ((339697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143548139169/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((339697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c36 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((246719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12671/312500) (δ := 207/100000000) (ψ := -100683/250000) 35 20
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t36 : ((411177335529/2500000000000 : ℚ) : ℝ) ≤ stT35 36 := by
  have hc : ((493413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411177335529/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((493413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c37 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((86929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1401441/5000000) (δ := 307/100000000) (ψ := -100683/250000) 35 20
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t37 : ((142893879891/2000000000000 : ℚ) : ℝ) ≤ stT35 37 := by
  have hc : ((86919/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142893879891/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((86919/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c38 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-232549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2568177/5000000) (δ := 113/50000000) (ψ := -100683/250000) 35 20
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t38 : ((-37728503141/500000000000 : ℚ) : ℝ) ≤ stT35 38 := by
  have hc : ((-116287/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37728503141/500000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-116287/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c39 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-123027/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7409209/10000000) (δ := 177/100000000) (ψ := -100683/250000) 35 20
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t39 : ((-394021857253/2500000000000 : ℚ) : ℝ) ≤ stT35 39 := by
  have hc : ((-492133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394021857253/2500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-492133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c40 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-30381/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3041723/5000000) (δ := 207/100000000) (ψ := -100683/250000) 35 21
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t40 : ((-48039746237/400000000000 : ℚ) : ℝ) ≤ stT35 40 := by
  have hc : ((-30383/40000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48039746237/400000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-30383/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c41 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((1659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3922843/10000000) (δ := 227/100000000) (ψ := -100683/250000) 35 21
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t41 : ((2512834833/10000000000000 : ℚ) : ℝ) ≤ stT35 41 := by
  have hc : ((1609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2512834833/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((1609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c42 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((37401/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1814307/10000000) (δ := 143/50000000) (ψ := -100683/250000) 35 21
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t42 : ((115414239301/1000000000000 : ℚ) : ℝ) ≤ stT35 42 := by
  have hc : ((74797/100000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115414239301/1000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((74797/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c43 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((995217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 244611/10000000) (δ := 79/25000000) (ψ := -100683/250000) 35 21
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t43 : ((303522949499/2000000000000 : ℚ) : ℝ) ≤ stT35 43 := by
  have hc : ((995167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303522949499/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((995167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c44 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((619667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1128097/5000000) (δ := 123/50000000) (ψ := -100683/250000) 35 21
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t44 : ((233526831513/2500000000000 : ℚ) : ℝ) ≤ stT35 44 := by
  have hc : ((619617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233526831513/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((619617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c45 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-29489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4222569/10000000) (δ := 307/100000000) (ψ := -100683/250000) 35 21
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t45 : ((-10994560017/625000000000 : ℚ) : ℝ) ≤ stT35 45 := by
  have hc : ((-59003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10994560017/625000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-59003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c46 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-193873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1536431/2500000) (δ := 357/100000000) (ψ := -100683/250000) 35 21
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t46 : ((-28586865891/250000000000 : ℚ) : ℝ) ≤ stT35 46 := by
  have hc : ((-387771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28586865891/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-387771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c47 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-124699/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7680447/10000000) (δ := 89/25000000) (ψ := -100683/250000) 35 22
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t47 : ((-14552105033/100000000000 : ℚ) : ℝ) ≤ stT35 47 := by
  have hc : ((-498821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14552105033/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-498821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c48 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-346093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5838273/10000000) (δ := 37/12500000) (ψ := -100683/250000) 35 22
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t48 : ((-15611825449/156250000000 : ℚ) : ℝ) ≤ stT35 48 := by
  have hc : ((-173059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15611825449/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-173059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c49 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-1713/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2017043/5000000) (δ := 337/100000000) (ψ := -100683/250000) 35 22
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t49 : ((-122500049/20000000000 : ℚ) : ℝ) ≤ stT35 49 := by
  have hc : ((-343/8000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122500049/20000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-343/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c50 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((308237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2266349/10000000) (δ := 21/6250000) (ψ := -100683/250000) 35 22
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t50 : ((108969354289/1250000000000 : ℚ) : ℝ) ≤ stT35 50 := by
  have hc : ((77053/125000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108969354289/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((77053/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c51 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((488653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -533619/10000000) (δ := 59/25000000) (ψ := -100683/250000) 35 22
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t51 : ((4276350099/31250000000 : ℚ) : ℝ) ≤ stT35 51 := by
  have hc : ((122157/125000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4276350099/31250000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((122157/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c52 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((893289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1165463/10000000) (δ := 153/50000000) (ψ := -100683/250000) 35 22
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t52 : ((4954796733/40000000000 : ℚ) : ℝ) ≤ stT35 52 := by
  have hc : ((893239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4954796733/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((893239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c53 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((21203/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2832181/10000000) (δ := 143/50000000) (ψ := -100683/250000) 35 22
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t53 : ((11648445121/200000000000 : ℚ) : ℝ) ≤ stT35 53 := by
  have hc : ((42401/100000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11648445121/200000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((42401/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c54 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-107309/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2233871/5000000) (δ := 49/25000000) (ψ := -100683/250000) 35 22
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t54 : ((-18257889069/625000000000 : ℚ) : ℝ) ≤ stT35 54 := by
  have hc : ((-53667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18257889069/625000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-53667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c55 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-189219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1518323/2500000) (δ := 307/100000000) (ψ := -100683/250000) 35 22
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t55 : ((-1275798773/12500000000 : ℚ) : ℝ) ≤ stT35 55 := by
  have hc : ((-378463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1275798773/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-378463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c56 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-99667/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7649911/10000000) (δ := 317/100000000) (ψ := -100683/250000) 35 22
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t56 : ((-16649048913/125000000000 : ℚ) : ℝ) ≤ stT35 56 := by
  have hc : ((-12459/12500 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16649048913/125000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-12459/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c57 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-107351/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6509339/10000000) (δ := 31/12500000) (ψ := -100683/250000) 35 23
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t57 : ((-568792881657/5000000000000 : ℚ) : ℝ) ≤ stT35 57 := by
  have hc : ((-429429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568792881657/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-429429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c58 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-205809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2493781/5000000) (δ := 13/4000000) (ψ := -100683/250000) 35 23
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t58 : ((-27027342121/500000000000 : ℚ) : ℝ) ≤ stT35 58 := by
  have hc : ((-102917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27027342121/500000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-102917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c59 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((173199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3491799/10000000) (δ := 41/20000000) (ψ := -100683/250000) 35 23
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t59 : ((225420778461/10000000000000 : ℚ) : ℝ) ≤ stT35 59 := by
  have hc : ((173149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225420778461/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((173149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c60 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((138121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252647/1250000) (δ := 109/50000000) (ψ := -100683/250000) 35 23
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t60 : ((89150236167/1000000000000 : ℚ) : ℝ) ≤ stT35 60 := by
  have hc : ((138111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89150236167/1000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((138111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c61 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((973679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287431/5000000) (δ := 57/25000000) (ψ := -100683/250000) 35 23
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t61 : ((77912713467/625000000000 : ℚ) : ℝ) ≤ stT35 61 := by
  have hc : ((973629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77912713467/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((973629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c62 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((94303/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 423967/5000000) (δ := 159/50000000) (ψ := -100683/250000) 35 23
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t62 : ((59879277149/500000000000 : ℚ) : ℝ) ≤ stT35 62 := by
  have hc : ((47149/50000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59879277149/500000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((47149/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c63 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((77781/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2247963/10000000) (δ := 11/4000000) (ψ := -100683/250000) 35 23
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t63 : ((391947719219/5000000000000 : ℚ) : ℝ) ≤ stT35 63 := by
  have hc : ((311099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391947719219/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((311099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c64 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((1877/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 725189/2000000) (δ := 77/25000000) (ψ := -100683/250000) 35 23
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t64 : ((60039/4000000 : ℚ) : ℝ) ≤ stT35 64 := by
  have hc : ((60039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60039/4000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((60039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c65 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-204897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4982561/10000000) (δ := 31/12500000) (ψ := -100683/250000) 35 23
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t65 : ((-31771824107/625000000000 : ℚ) : ℝ) ≤ stT35 65 := by
  have hc : ((-102461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31771824107/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-102461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c66 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-817231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1263693/2000000) (δ := 39/20000000) (ψ := -100683/250000) 35 23
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t66 : ((-201200688423/2000000000000 : ℚ) : ℝ) ≤ stT35 66 := by
  have hc : ((-817281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201200688423/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-817281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c67 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-996141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7634279/10000000) (δ := 57/20000000) (ψ := -100683/250000) 35 23
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t67 : ((-243408312749/2000000000000 : ℚ) : ℝ) ≤ stT35 67 := by
  have hc : ((-996191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243408312749/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-996191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c68 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-113587/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1694341/2500000) (δ := 81/25000000) (ψ := -100683/250000) 35 24
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t68 : ((-551008595267/5000000000000 : ℚ) : ℝ) ≤ stT35 68 := by
  have hc : ((-454373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551008595267/5000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-454373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c69 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-588491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5499969/10000000) (δ := 81/25000000) (ψ := -100683/250000) 35 24
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t69 : ((-708520379719/10000000000000 : ℚ) : ℝ) ≤ stT35 69 := by
  have hc : ((-588541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-708520379719/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-588541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c70 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-15657/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -848191/2000000) (δ := 107/50000000) (ψ := -100683/250000) 35 24
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t70 : ((-74884682537/5000000000000 : ℚ) : ℝ) ≤ stT35 70 := by
  have hc : ((-62653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74884682537/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-62653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c71 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((362433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2999799/10000000) (δ := 279/100000000) (ψ := -100683/250000) 35 24
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t71 : ((430069259123/10000000000000 : ℚ) : ℝ) ≤ stT35 71 := by
  have hc : ((362383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430069259123/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((362383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c72 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((7581/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1776003/10000000) (δ := 71/25000000) (ψ := -100683/250000) 35 24
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t72 : ((17867405271/200000000000 : ℚ) : ℝ) ≤ stT35 72 := by
  have hc : ((15161/20000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17867405271/200000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((15161/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c73 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((974203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -569087/10000000) (δ := 97/50000000) (ψ := -100683/250000) 35 24
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t73 : ((1140159386883/10000000000000 : ℚ) : ℝ) ≤ stT35 73 := by
  have hc : ((974153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1140159386883/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((974153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c74 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((969267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621407/10000000) (δ := 319/100000000) (ψ := -100683/250000) 35 24
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t74 : ((281672875323/2500000000000 : ℚ) : ℝ) ≤ stT35 74 := by
  have hc : ((969217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281672875323/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((969217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c75 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((9411/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 897961/5000000) (δ := 71/25000000) (ψ := -100683/250000) 35 24
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t75 : ((869292801/10000000000 : ℚ) : ℝ) ≤ stT35 75 := by
  have hc : ((75283/100000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((869292801/10000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((75283/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c76 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((4739/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2954879/10000000) (δ := 51/25000000) (ψ := -100683/250000) 35 24
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t76 : ((21741142873/500000000000 : ℚ) : ℝ) ≤ stT35 76 := by
  have hc : ((37907/100000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21741142873/500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((37907/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c77 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-4289/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2049343/5000000) (δ := 137/50000000) (ψ := -100683/250000) 35 24
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t77 : ((-19565325611/2500000000000 : ℚ) : ℝ) ≤ stT35 77 := by
  have hc : ((-34337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19565325611/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-34337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c78 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-248569/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2613867/5000000) (δ := 127/50000000) (ψ := -100683/250000) 35 24
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t78 : ((-70369379283/1250000000000 : ℚ) : ℝ) ≤ stT35 78 := by
  have hc : ((-124297/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70369379283/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-124297/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c79 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-822711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6342399/10000000) (δ := 199/100000000) (ψ := -100683/250000) 35 24
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t79 : ((-28927453999/312500000000 : ℚ) : ℝ) ≤ stT35 79 := by
  have hc : ((-822761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28927453999/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-822761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c80 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-986521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3721521/5000000) (δ := 117/50000000) (ψ := -100683/250000) 35 24
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t80 : ((-551509960707/5000000000000 : ℚ) : ℝ) ≤ stT35 80 := by
  have hc : ((-986571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551509960707/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-986571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c81 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-963661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7177951/10000000) (δ := 179/100000000) (ψ := -100683/250000) 35 25
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t81 : ((-133848857079/1250000000000 : ℚ) : ℝ) ≤ stT35 81 := by
  have hc : ((-963711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133848857079/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-963711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c82 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-764929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3052159/5000000) (δ := 51/25000000) (ψ := -100683/250000) 35 25
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t82 : ((-211194637341/2500000000000 : ℚ) : ℝ) ≤ stT35 82 := by
  have hc : ((-764979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211194637341/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-764979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c83 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-431977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5043699/10000000) (δ := 43/12500000) (ψ := -100683/250000) 35 25
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t83 : ((-474211412361/10000000000000 : ℚ) : ℝ) ≤ stT35 83 := by
  have hc : ((-432027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474211412361/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-432027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c84 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-27513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1997891/5000000) (δ := 91/25000000) (ψ := -100683/250000) 35 25
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t84 : ((-3007371367/1000000000000 : ℚ) : ℝ) ≤ stT35 84 := by
  have hc : ((-27563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3007371367/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-27563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c85 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((94281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2960267/10000000) (δ := 189/100000000) (ψ := -100683/250000) 35 25
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t85 : ((51124258531/1250000000000 : ℚ) : ℝ) ≤ stT35 85 := by
  have hc : ((188537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51124258531/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((188537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c86 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((714599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936863/10000000) (δ := 349/100000000) (ψ := -100683/250000) 35 25
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t86 : ((770517479523/10000000000000 : ℚ) : ℝ) ≤ stT35 86 := by
  have hc : ((714549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((770517479523/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((714549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c87 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((186457/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -925291/10000000) (δ := 137/50000000) (ψ := -100683/250000) 35 25
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t87 : ((12493254129/125000000000 : ℚ) : ℝ) ≤ stT35 87 := by
  have hc : ((186447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12493254129/125000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((186447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c88 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((999553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467/62500) (δ := 71/25000000) (ψ := -100683/250000) 35 25
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t88 : ((1065473196509/10000000000000 : ℚ) : ℝ) ≤ stT35 88 := by
  have hc : ((999503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1065473196509/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((999503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c89 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((182177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1063431/10000000) (δ := 259/100000000) (ψ := -100683/250000) 35 25
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t89 : ((193096473499/2000000000000 : ℚ) : ℝ) ≤ stT35 89 := by
  have hc : ((182167/200000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193096473499/2000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((182167/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c90 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((342411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1020547/5000000) (δ := 229/100000000) (ψ := -100683/250000) 35 25
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t90 : ((45113292939/625000000000 : ℚ) : ℝ) ≤ stT35 90 := by
  have hc : ((171193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45113292939/625000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((171193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c91 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((35939/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 601591/2000000) (δ := 369/100000000) (ψ := -100683/250000) 35 25
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t91 : ((4708629657/125000000000 : ℚ) : ℝ) ≤ stT35 91 := by
  have hc : ((17967/50000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4708629657/125000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((17967/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c92 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-14903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3964249/10000000) (δ := 279/100000000) (ψ := -100683/250000) 35 25
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t92 : ((-15589594069/10000000000000 : ℚ) : ℝ) ≤ stT35 92 := by
  have hc : ((-14953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15589594069/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-14953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c93 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-15329/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1227551/2500000) (δ := 329/100000000) (ψ := -100683/250000) 35 25
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t93 : ((-1987188889/50000000000 : ℚ) : ℝ) ≤ stT35 93 := by
  have hc : ((-15331/40000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1987188889/50000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-15331/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c94 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-27777/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2923021/5000000) (δ := 299/100000000) (ψ := -100683/250000) 35 25
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t94 : ((-14325935869/200000000000 : ℚ) : ℝ) ≤ stT35 94 := by
  have hc : ((-27779/40000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14325935869/200000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-27779/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c95 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-453897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 846497/1250000) (δ := 309/100000000) (ψ := -100683/250000) 35 25
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t95 : ((-232857219819/2500000000000 : ℚ) : ℝ) ≤ stT35 95 := by
  have hc : ((-226961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232857219819/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-226961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c96 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-997803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1537643/2000000) (δ := 319/100000000) (ψ := -100683/250000) 35 25
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t96 : ((-1018429726713/10000000000000 : ℚ) : ℝ) ≤ stT35 96 := by
  have hc : ((-997853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1018429726713/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-997853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c97 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-956397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1778251/2500000) (δ := 29/10000000) (ψ := -100683/250000) 35 26
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t97 : ((-971125592109/10000000000000 : ℚ) : ℝ) ≤ stT35 97 := by
  have hc : ((-956447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-971125592109/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-956447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c98 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-99103/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6215561/10000000) (δ := 13/5000000) (ψ := -100683/250000) 35 26
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t98 : ((-400462024861/5000000000000 : ℚ) : ℝ) ≤ stT35 98 := by
  have hc : ((-396437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400462024861/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-396437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c99 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-531267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1331807/2500000) (δ := 9/5000000) (ψ := -100683/250000) 35 26
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t99 : ((-266996887523/5000000000000 : ℚ) : ℝ) ≤ stT35 99 := by
  have hc : ((-531317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266996887523/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-531317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_c100 :
    |Real.cos (((35 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-100683/250000 : ℚ) : ℝ))
      - ((-20683/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277989/625000) (δ := 29/10000000) (ψ := -100683/250000) 35 26
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st35_t100 : ((-1293/62500 : ℚ) : ℝ) ≤ stT35 100 := by
  have hc : ((-1293/6250 : ℚ) : ℝ)
      ≤ Real.cos (((35 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-100683/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st35_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1293/62500 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-1293/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st35_p1 : ((114993/125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT35 (i+1) := by
  rw [Finset.sum_range_one]
  exact st35_t1

theorem st35_p2 : ((15503883129061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT35 (i+1))
      = (∑ i ∈ Finset.range 1, stT35 (i+1)) + stT35 2 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 1
    simpa using h
  have hprev := st35_p1
  have hstep := st35_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p3 : ((3567070050741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT35 (i+1))
      = (∑ i ∈ Finset.range 2, stT35 (i+1)) + stT35 3 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 2
    simpa using h
  have hprev := st35_p2
  have hstep := st35_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p4 : ((3793389050741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT35 (i+1))
      = (∑ i ∈ Finset.range 3, stT35 (i+1)) + stT35 4 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 3
    simpa using h
  have hprev := st35_p3
  have hstep := st35_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p5 : ((4672609002887/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT35 (i+1))
      = (∑ i ∈ Finset.range 4, stT35 (i+1)) + stT35 5 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 4
    simpa using h
  have hprev := st35_p4
  have hstep := st35_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p6 : ((27283546376121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT35 (i+1))
      = (∑ i ∈ Finset.range 5, stT35 (i+1)) + stT35 6 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 5
    simpa using h
  have hprev := st35_p5
  have hstep := st35_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p7 : ((30391150774701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT35 (i+1))
      = (∑ i ∈ Finset.range 6, stT35 (i+1)) + stT35 7 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 6
    simpa using h
  have hprev := st35_p6
  have hstep := st35_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p8 : ((28267560561873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT35 (i+1))
      = (∑ i ∈ Finset.range 7, stT35 (i+1)) + stT35 8 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 7
    simpa using h
  have hprev := st35_p7
  have hstep := st35_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p9 : ((27166550341671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT35 (i+1))
      = (∑ i ∈ Finset.range 8, stT35 (i+1)) + stT35 9 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 8
    simpa using h
  have hprev := st35_p8
  have hstep := st35_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p10 : ((1850556657633/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT35 (i+1))
      = (∑ i ∈ Finset.range 9, stT35 (i+1)) + stT35 10 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 9
    simpa using h
  have hprev := st35_p9
  have hstep := st35_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p11 : ((3369253285299/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT35 (i+1))
      = (∑ i ∈ Finset.range 10, stT35 (i+1)) + stT35 11 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 10
    simpa using h
  have hprev := st35_p10
  have hstep := st35_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p12 : ((29352393861461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT35 (i+1))
      = (∑ i ∈ Finset.range 11, stT35 (i+1)) + stT35 12 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 11
    simpa using h
  have hprev := st35_p11
  have hstep := st35_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p13 : ((27694666766759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT35 (i+1))
      = (∑ i ∈ Finset.range 12, stT35 (i+1)) + stT35 13 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 12
    simpa using h
  have hprev := st35_p12
  have hstep := st35_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p14 : ((27942075804823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT35 (i+1))
      = (∑ i ∈ Finset.range 13, stT35 (i+1)) + stT35 14 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 13
    simpa using h
  have hprev := st35_p13
  have hstep := st35_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p15 : ((29471624840119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT35 (i+1))
      = (∑ i ∈ Finset.range 14, stT35 (i+1)) + stT35 15 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 14
    simpa using h
  have hprev := st35_p14
  have hstep := st35_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p16 : ((1079005553661/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT35 (i+1))
      = (∑ i ∈ Finset.range 15, stT35 (i+1)) + stT35 16 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 15
    simpa using h
  have hprev := st35_p15
  have hstep := st35_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p17 : ((28354528536897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT35 (i+1))
      = (∑ i ∈ Finset.range 16, stT35 (i+1)) + stT35 17 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 16
    simpa using h
  have hprev := st35_p16
  have hstep := st35_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p18 : ((29558179533549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT35 (i+1))
      = (∑ i ∈ Finset.range 17, stT35 (i+1)) + stT35 18 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 17
    simpa using h
  have hprev := st35_p17
  have hstep := st35_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p19 : ((27316463691271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT35 (i+1))
      = (∑ i ∈ Finset.range 18, stT35 (i+1)) + stT35 19 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 18
    simpa using h
  have hprev := st35_p18
  have hstep := st35_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p20 : ((2733872821039/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT35 (i+1))
      = (∑ i ∈ Finset.range 19, stT35 (i+1)) + stT35 20 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 19
    simpa using h
  have hprev := st35_p19
  have hstep := st35_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p21 : ((14748651886571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT35 (i+1))
      = (∑ i ∈ Finset.range 20, stT35 (i+1)) + stT35 21 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 20
    simpa using h
  have hprev := st35_p20
  have hstep := st35_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p22 : ((2906471082191/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT35 (i+1))
      = (∑ i ∈ Finset.range 21, stT35 (i+1)) + stT35 22 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 21
    simpa using h
  have hprev := st35_p21
  have hstep := st35_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p23 : ((5403340867901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT35 (i+1))
      = (∑ i ∈ Finset.range 22, stT35 (i+1)) + stT35 23 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 22
    simpa using h
  have hprev := st35_p22
  have hstep := st35_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p24 : ((27236782779161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT35 (i+1))
      = (∑ i ∈ Finset.range 23, stT35 (i+1)) + stT35 24 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 23
    simpa using h
  have hprev := st35_p23
  have hstep := st35_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p25 : ((29235530779161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT35 (i+1))
      = (∑ i ∈ Finset.range 24, stT35 (i+1)) + stT35 25 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 24
    simpa using h
  have hprev := st35_p24
  have hstep := st35_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p26 : ((3710798985907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT35 (i+1))
      = (∑ i ∈ Finset.range 25, stT35 (i+1)) + stT35 26 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 25
    simpa using h
  have hprev := st35_p25
  have hstep := st35_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p27 : ((27980970307593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT35 (i+1))
      = (∑ i ∈ Finset.range 26, stT35 (i+1)) + stT35 27 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 26
    simpa using h
  have hprev := st35_p26
  have hstep := st35_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p28 : ((26652024096117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT35 (i+1))
      = (∑ i ∈ Finset.range 27, stT35 (i+1)) + stT35 28 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 27
    simpa using h
  have hprev := st35_p27
  have hstep := st35_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p29 : ((27456901804437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT35 (i+1))
      = (∑ i ∈ Finset.range 28, stT35 (i+1)) + stT35 29 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 28
    simpa using h
  have hprev := st35_p28
  have hstep := st35_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p30 : ((1829924976227/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT35 (i+1))
      = (∑ i ∈ Finset.range 29, stT35 (i+1)) + stT35 30 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 29
    simpa using h
  have hprev := st35_p29
  have hstep := st35_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p31 : ((29909787163539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT35 (i+1))
      = (∑ i ∈ Finset.range 30, stT35 (i+1)) + stT35 31 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 30
    simpa using h
  have hprev := st35_p30
  have hstep := st35_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p32 : ((28701914398847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT35 (i+1))
      = (∑ i ∈ Finset.range 31, stT35 (i+1)) + stT35 32 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 31
    simpa using h
  have hprev := st35_p31
  have hstep := st35_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p33 : ((27018837193289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT35 (i+1))
      = (∑ i ∈ Finset.range 32, stT35 (i+1)) + stT35 33 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 32
    simpa using h
  have hprev := st35_p32
  have hstep := st35_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p34 : ((26565346875281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT35 (i+1))
      = (∑ i ∈ Finset.range 33, stT35 (i+1)) + stT35 34 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 33
    simpa using h
  have hprev := st35_p33
  have hstep := st35_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p35 : ((27713731988633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT35 (i+1))
      = (∑ i ∈ Finset.range 34, stT35 (i+1)) + stT35 35 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 34
    simpa using h
  have hprev := st35_p34
  have hstep := st35_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p36 : ((29358441330749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT35 (i+1))
      = (∑ i ∈ Finset.range 35, stT35 (i+1)) + stT35 36 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 35
    simpa using h
  have hprev := st35_p35
  have hstep := st35_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p37 : ((7518227682551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT35 (i+1))
      = (∑ i ∈ Finset.range 36, stT35 (i+1)) + stT35 37 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 36
    simpa using h
  have hprev := st35_p36
  have hstep := st35_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p38 : ((3664792583423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT35 (i+1))
      = (∑ i ∈ Finset.range 37, stT35 (i+1)) + stT35 38 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 37
    simpa using h
  have hprev := st35_p37
  have hstep := st35_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p39 : ((6935563309593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT35 (i+1))
      = (∑ i ∈ Finset.range 38, stT35 (i+1)) + stT35 39 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 38
    simpa using h
  have hprev := st35_p38
  have hstep := st35_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p40 : ((26541259582447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT35 (i+1))
      = (∑ i ∈ Finset.range 39, stT35 (i+1)) + stT35 40 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 39
    simpa using h
  have hprev := st35_p39
  have hstep := st35_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p41 : ((20737322201/7812500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT35 (i+1))
      = (∑ i ∈ Finset.range 40, stT35 (i+1)) + stT35 41 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 40
    simpa using h
  have hprev := st35_p40
  have hstep := st35_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p42 : ((2769791481029/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT35 (i+1))
      = (∑ i ∈ Finset.range 41, stT35 (i+1)) + stT35 42 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 41
    simpa using h
  have hprev := st35_p41
  have hstep := st35_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p43 : ((5843105911557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT35 (i+1))
      = (∑ i ∈ Finset.range 42, stT35 (i+1)) + stT35 43 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 42
    simpa using h
  have hprev := st35_p42
  have hstep := st35_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p44 : ((30149636883837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT35 (i+1))
      = (∑ i ∈ Finset.range 43, stT35 (i+1)) + stT35 44 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 43
    simpa using h
  have hprev := st35_p43
  have hstep := st35_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p45 : ((5994744784713/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT35 (i+1))
      = (∑ i ∈ Finset.range 44, stT35 (i+1)) + stT35 45 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 44
    simpa using h
  have hprev := st35_p44
  have hstep := st35_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p46 : ((1153209971517/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT35 (i+1))
      = (∑ i ∈ Finset.range 45, stT35 (i+1)) + stT35 46 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 45
    simpa using h
  have hprev := st35_p45
  have hstep := st35_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p47 : ((219000310277/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT35 (i+1))
      = (∑ i ∈ Finset.range 46, stT35 (i+1)) + stT35 47 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 46
    simpa using h
  have hprev := st35_p46
  have hstep := st35_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p48 : ((26375881955889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT35 (i+1))
      = (∑ i ∈ Finset.range 47, stT35 (i+1)) + stT35 48 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 47
    simpa using h
  have hprev := st35_p47
  have hstep := st35_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p49 : ((26314631931389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT35 (i+1))
      = (∑ i ∈ Finset.range 48, stT35 (i+1)) + stT35 49 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 48
    simpa using h
  have hprev := st35_p48
  have hstep := st35_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p50 : ((27186386765701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT35 (i+1))
      = (∑ i ∈ Finset.range 49, stT35 (i+1)) + stT35 50 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 49
    simpa using h
  have hprev := st35_p49
  have hstep := st35_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p51 : ((28554818797381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT35 (i+1))
      = (∑ i ∈ Finset.range 50, stT35 (i+1)) + stT35 51 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 50
    simpa using h
  have hprev := st35_p50
  have hstep := st35_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p52 : ((29793517980631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT35 (i+1))
      = (∑ i ∈ Finset.range 51, stT35 (i+1)) + stT35 52 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 51
    simpa using h
  have hprev := st35_p51
  have hstep := st35_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p53 : ((30375940236681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT35 (i+1))
      = (∑ i ∈ Finset.range 52, stT35 (i+1)) + stT35 53 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 52
    simpa using h
  have hprev := st35_p52
  have hstep := st35_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p54 : ((30083814011577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT35 (i+1))
      = (∑ i ∈ Finset.range 53, stT35 (i+1)) + stT35 54 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 53
    simpa using h
  have hprev := st35_p53
  have hstep := st35_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p55 : ((29063174993177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT35 (i+1))
      = (∑ i ∈ Finset.range 54, stT35 (i+1)) + stT35 55 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 54
    simpa using h
  have hprev := st35_p54
  have hstep := st35_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p56 : ((27731251080137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT35 (i+1))
      = (∑ i ∈ Finset.range 55, stT35 (i+1)) + stT35 56 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 55
    simpa using h
  have hprev := st35_p55
  have hstep := st35_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p57 : ((26593665316823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT35 (i+1))
      = (∑ i ∈ Finset.range 56, stT35 (i+1)) + stT35 57 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 56
    simpa using h
  have hprev := st35_p56
  have hstep := st35_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p58 : ((26053118474403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT35 (i+1))
      = (∑ i ∈ Finset.range 57, stT35 (i+1)) + stT35 58 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 57
    simpa using h
  have hprev := st35_p57
  have hstep := st35_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p59 : ((205301087913/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT35 (i+1))
      = (∑ i ∈ Finset.range 58, stT35 (i+1)) + stT35 59 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 58
    simpa using h
  have hprev := st35_p58
  have hstep := st35_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p60 : ((13585020807267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT35 (i+1))
      = (∑ i ∈ Finset.range 59, stT35 (i+1)) + stT35 60 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 59
    simpa using h
  have hprev := st35_p59
  have hstep := st35_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p61 : ((14208322515003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT35 (i+1))
      = (∑ i ∈ Finset.range 60, stT35 (i+1)) + stT35 61 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 60
    simpa using h
  have hprev := st35_p60
  have hstep := st35_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p62 : ((14807115286493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT35 (i+1))
      = (∑ i ∈ Finset.range 61, stT35 (i+1)) + stT35 62 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 61
    simpa using h
  have hprev := st35_p61
  have hstep := st35_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p63 : ((949941437857/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT35 (i+1))
      = (∑ i ∈ Finset.range 62, stT35 (i+1)) + stT35 63 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 62
    simpa using h
  have hprev := st35_p62
  have hstep := st35_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p64 : ((238657996183/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT35 (i+1))
      = (∑ i ∈ Finset.range 63, stT35 (i+1)) + stT35 64 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 63
    simpa using h
  have hprev := st35_p63
  have hstep := st35_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p65 : ((1877492145357/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT35 (i+1))
      = (∑ i ∈ Finset.range 64, stT35 (i+1)) + stT35 65 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 64
    simpa using h
  have hprev := st35_p64
  have hstep := st35_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p66 : ((29033870883597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT35 (i+1))
      = (∑ i ∈ Finset.range 65, stT35 (i+1)) + stT35 66 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 65
    simpa using h
  have hprev := st35_p65
  have hstep := st35_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p67 : ((6954207329963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT35 (i+1))
      = (∑ i ∈ Finset.range 66, stT35 (i+1)) + stT35 67 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 66
    simpa using h
  have hprev := st35_p66
  have hstep := st35_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p68 : ((13357406064659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT35 (i+1))
      = (∑ i ∈ Finset.range 67, stT35 (i+1)) + stT35 68 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 67
    simpa using h
  have hprev := st35_p67
  have hstep := st35_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p69 : ((26006291749599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT35 (i+1))
      = (∑ i ∈ Finset.range 68, stT35 (i+1)) + stT35 69 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 68
    simpa using h
  have hprev := st35_p68
  have hstep := st35_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p70 : ((1034260895381/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT35 (i+1))
      = (∑ i ∈ Finset.range 69, stT35 (i+1)) + stT35 70 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 69
    simpa using h
  have hprev := st35_p69
  have hstep := st35_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p71 : ((6417624913/2441406250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT35 (i+1))
      = (∑ i ∈ Finset.range 70, stT35 (i+1)) + stT35 71 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 70
    simpa using h
  have hprev := st35_p70
  have hstep := st35_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p72 : ((13589980953599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT35 (i+1))
      = (∑ i ∈ Finset.range 71, stT35 (i+1)) + stT35 72 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 71
    simpa using h
  have hprev := st35_p71
  have hstep := st35_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p73 : ((28320121294081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT35 (i+1))
      = (∑ i ∈ Finset.range 72, stT35 (i+1)) + stT35 73 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 72
    simpa using h
  have hprev := st35_p72
  have hstep := st35_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p74 : ((29446812795373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT35 (i+1))
      = (∑ i ∈ Finset.range 73, stT35 (i+1)) + stT35 74 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 73
    simpa using h
  have hprev := st35_p73
  have hstep := st35_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p75 : ((30316105596373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT35 (i+1))
      = (∑ i ∈ Finset.range 74, stT35 (i+1)) + stT35 75 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 74
    simpa using h
  have hprev := st35_p74
  have hstep := st35_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p76 : ((30750928453833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT35 (i+1))
      = (∑ i ∈ Finset.range 75, stT35 (i+1)) + stT35 76 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 75
    simpa using h
  have hprev := st35_p75
  have hstep := st35_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p77 : ((30672667151389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT35 (i+1))
      = (∑ i ∈ Finset.range 76, stT35 (i+1)) + stT35 77 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 76
    simpa using h
  have hprev := st35_p76
  have hstep := st35_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p78 : ((240877696937/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT35 (i+1))
      = (∑ i ∈ Finset.range 77, stT35 (i+1)) + stT35 78 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 77
    simpa using h
  have hprev := st35_p77
  have hstep := st35_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p79 : ((29184033589157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT35 (i+1))
      = (∑ i ∈ Finset.range 78, stT35 (i+1)) + stT35 79 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 78
    simpa using h
  have hprev := st35_p78
  have hstep := st35_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p80 : ((28081013667743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT35 (i+1))
      = (∑ i ∈ Finset.range 79, stT35 (i+1)) + stT35 80 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 79
    simpa using h
  have hprev := st35_p79
  have hstep := st35_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p81 : ((27010222811111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT35 (i+1))
      = (∑ i ∈ Finset.range 80, stT35 (i+1)) + stT35 81 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 80
    simpa using h
  have hprev := st35_p80
  have hstep := st35_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p82 : ((26165444261747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT35 (i+1))
      = (∑ i ∈ Finset.range 81, stT35 (i+1)) + stT35 82 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 81
    simpa using h
  have hprev := st35_p81
  have hstep := st35_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p83 : ((12845616424693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT35 (i+1))
      = (∑ i ∈ Finset.range 82, stT35 (i+1)) + stT35 83 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 82
    simpa using h
  have hprev := st35_p82
  have hstep := st35_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p84 : ((6415289783929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT35 (i+1))
      = (∑ i ∈ Finset.range 83, stT35 (i+1)) + stT35 84 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 83
    simpa using h
  have hprev := st35_p83
  have hstep := st35_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p85 : ((6517538300991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT35 (i+1))
      = (∑ i ∈ Finset.range 84, stT35 (i+1)) + stT35 85 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 84
    simpa using h
  have hprev := st35_p84
  have hstep := st35_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p86 : ((26840670683487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT35 (i+1))
      = (∑ i ∈ Finset.range 85, stT35 (i+1)) + stT35 86 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 85
    simpa using h
  have hprev := st35_p85
  have hstep := st35_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p87 : ((27840131013807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT35 (i+1))
      = (∑ i ∈ Finset.range 86, stT35 (i+1)) + stT35 87 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 86
    simpa using h
  have hprev := st35_p86
  have hstep := st35_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p88 : ((7226401052579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT35 (i+1))
      = (∑ i ∈ Finset.range 87, stT35 (i+1)) + stT35 88 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 87
    simpa using h
  have hprev := st35_p87
  have hstep := st35_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p89 : ((29871086577811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT35 (i+1))
      = (∑ i ∈ Finset.range 88, stT35 (i+1)) + stT35 89 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 88
    simpa using h
  have hprev := st35_p88
  have hstep := st35_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p90 : ((6118579852967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT35 (i+1))
      = (∑ i ∈ Finset.range 89, stT35 (i+1)) + stT35 90 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 89
    simpa using h
  have hprev := st35_p89
  have hstep := st35_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p91 : ((6193917927479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT35 (i+1))
      = (∑ i ∈ Finset.range 90, stT35 (i+1)) + stT35 91 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 90
    simpa using h
  have hprev := st35_p90
  have hstep := st35_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p92 : ((15477000021663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT35 (i+1))
      = (∑ i ∈ Finset.range 91, stT35 (i+1)) + stT35 92 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 91
    simpa using h
  have hprev := st35_p91
  have hstep := st35_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p93 : ((15278281132763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT35 (i+1))
      = (∑ i ∈ Finset.range 92, stT35 (i+1)) + stT35 93 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 92
    simpa using h
  have hprev := st35_p92
  have hstep := st35_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p94 : ((7460066368019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT35 (i+1))
      = (∑ i ∈ Finset.range 93, stT35 (i+1)) + stT35 94 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 93
    simpa using h
  have hprev := st35_p93
  have hstep := st35_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p95 : ((36136045741/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT35 (i+1))
      = (∑ i ∈ Finset.range 94, stT35 (i+1)) + stT35 95 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 94
    simpa using h
  have hprev := st35_p94
  have hstep := st35_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p96 : ((27890406866087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT35 (i+1))
      = (∑ i ∈ Finset.range 95, stT35 (i+1)) + stT35 96 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 95
    simpa using h
  have hprev := st35_p95
  have hstep := st35_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p97 : ((13459640636989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT35 (i+1))
      = (∑ i ∈ Finset.range 96, stT35 (i+1)) + stT35 97 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 96
    simpa using h
  have hprev := st35_p96
  have hstep := st35_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p98 : ((408099331629/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT35 (i+1))
      = (∑ i ∈ Finset.range 97, stT35 (i+1)) + stT35 98 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 97
    simpa using h
  have hprev := st35_p97
  have hstep := st35_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p99 : ((2558436344921/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT35 (i+1))
      = (∑ i ∈ Finset.range 98, stT35 (i+1)) + stT35 99 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 98
    simpa using h
  have hprev := st35_p98
  have hstep := st35_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st35_p100 : ((2537748344921/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT35 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT35 (i+1))
      = (∑ i ∈ Finset.range 99, stT35 (i+1)) + stT35 100 := by
    have h := Finset.sum_range_succ (fun i => stT35 (i+1)) 99
    simpa using h
  have hprev := st35_p99
  have hstep := st35_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 35`.** -/
theorem station_35_sign : 0 < hardyG (((35:ℕ)):ℝ) := by
  have hcore := phase_station_lower 35 100 (by norm_num) (by norm_num)
    ((-100683/250000 : ℚ) : ℝ)
  have hchain := st35_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT35 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((35:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-100683/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((35:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((35:ℕ)):ℝ)+1) * ((((35:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((627731/1400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2537748344921/1000000000000 : ℚ) : ℝ) - ((627731/1400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-100683/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((35:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-100683/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((35:ℕ)):ℝ))).re
      - Real.sin ((-100683/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((35:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((35:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((35:ℕ)):ℝ)
      = ((((35:ℕ)):ℝ) * (Real.log (((35:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((35:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_35
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
  have hθwin : |(((-100683/250000 : ℚ) : ℝ) + ((2:ℤ)) * (2*Real.pi)) - theta (((35:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((35:ℕ)):ℝ))
    (φ := ((-100683/250000 : ℚ) : ℝ) + ((2:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-100683/250000 : ℚ)) : ℝ) 2).1,
    (cos_sin_shift (((-100683/250000 : ℚ)) : ℝ) 2).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_35_sign
end AxiomAudit
