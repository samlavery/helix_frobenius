import RequestProject.DVPSqrtTable

/-!
# Station `t = 93` of the extended Hardy ladder (rung-109)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT93 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((93 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))

theorem st93_c1 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((495929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 319247/10000000) (δ := 21/100000000) (ψ := -127699/1000000) 93 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t1 : ((15497/15625 : ℚ) : ℝ) ≤ stT93 1 := by
  have hc : ((15497/15625 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15497/15625 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((15497/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c2 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-46659/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2198167/5000000) (δ := 739/100000000) (ψ := -127699/1000000) 93 10
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t2 : ((-165008675081/1250000000000 : ℚ) : ℝ) ≤ stT93 2 := by
  have hc : ((-93343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165008675081/1250000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-93343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c3 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-195611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 552399/1250000) (δ := 813/100000000) (ψ := -127699/1000000) 93 16
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t3 : ((-1129649370483/10000000000000 : ℚ) : ℝ) ≤ stT93 3 := by
  have hc : ((-195661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1129649370483/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-195661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c4 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-48473/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7234543/10000000) (δ := 537/100000000) (ψ := -127699/1000000) 93 21
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t4 : ((-484755096951/1000000000000 : ℚ) : ℝ) ≤ stT93 4 := by
  have hc : ((-96951/100000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484755096951/1000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-96951/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c5 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((273917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2477557/10000000) (δ := 211/25000000) (ψ := -127699/1000000) 93 24
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t5 : ((61244099971/250000000000 : ℚ) : ℝ) ≤ stT93 5 := by
  have hc : ((68473/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61244099971/250000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((68473/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c6 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-483589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1442337/2000000) (δ := 611/100000000) (ψ := -127699/1000000) 93 27
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t6 : ((-987172966781/2500000000000 : ℚ) : ℝ) ≤ stT93 6 := by
  have hc : ((-241807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-987172966781/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-241807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c7 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((440149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1393789/5000000) (δ := 491/100000000) (ψ := -127699/1000000) 93 29
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t7 : ((415854386189/2500000000000 : ℚ) : ℝ) ≤ stT93 7 := by
  have hc : ((440099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415854386189/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((440099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c8 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((4734/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197341/625000) (δ := 569/100000000) (ψ := -127699/1000000) 93 31
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t8 : ((535502434779/5000000000000 : ℚ) : ℝ) ≤ stT93 8 := by
  have hc : ((151463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535502434779/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((151463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c9 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-482407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7188827/10000000) (δ := 137/20000000) (ψ := -127699/1000000) 93 33
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t9 : ((-6281667923/19531250000 : ℚ) : ℝ) ≤ stT93 9 := by
  have hc : ((-15076/15625 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6281667923/19531250000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-15076/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c10 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((25069/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 159953/1000000) (δ := 423/50000000) (ψ := -127699/1000000) 93 34
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t10 : ((1268322896883/5000000000000 : ℚ) : ℝ) ≤ stT93 10 := by
  have hc : ((401079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1268322896883/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((401079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c11 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-996891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382839/500000) (δ := 647/100000000) (ψ := -127699/1000000) 93 36
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t11 : ((-1502945383137/5000000000000 : ℚ) : ℝ) ≤ stT93 11 := by
  have hc : ((-996941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1502945383137/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-996941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c12 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((311677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1567299/5000000) (δ := 99/20000000) (ψ := -127699/1000000) 93 37
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t12 : ((899589553877/10000000000000 : ℚ) : ℝ) ≤ stT93 12 := by
  have hc : ((311627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((899589553877/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((311627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c13 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((497837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29079/1250000) (δ := 499/100000000) (ψ := -127699/1000000) 93 38
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t13 : ((690340791/2500000000 : ℚ) : ℝ) ≤ stT93 13 := by
  have hc : ((124453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((690340791/2500000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((124453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c14 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((869897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1289509/10000000) (δ := 663/100000000) (ψ := -127699/1000000) 93 39
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t14 : ((581190882591/2500000000000 : ℚ) : ℝ) ≤ stT93 14 := by
  have hc : ((869847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((581190882591/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((869847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c15 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((199179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 405597/2500000) (δ := 943/100000000) (ψ := -127699/1000000) 93 40
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t15 : ((257122756501/1250000000000 : ℚ) : ℝ) ≤ stT93 15 := by
  have hc : ((398333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257122756501/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((398333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c16 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((466551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 919631/10000000) (δ := 371/50000000) (ψ := -127699/1000000) 93 41
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t16 : ((233263/1000000 : ℚ) : ℝ) ≤ stT93 16 := by
  have hc : ((233263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233263/1000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((233263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c17 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((480907/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173277/2500000) (δ := 551/100000000) (ψ := -127699/1000000) 93 42
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t17 : ((145788755499/625000000000 : ℚ) : ℝ) ≤ stT93 17 := by
  have hc : ((240441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145788755499/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((240441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c18 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((320351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155587/500000) (δ := 2/390625) (ψ := -127699/1000000) 93 43
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t18 : ((377478251811/5000000000000 : ℚ) : ℝ) ≤ stT93 18 := by
  have hc : ((320301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((377478251811/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((320301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c19 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-400461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3124537/5000000) (δ := 723/100000000) (ψ := -127699/1000000) 93 44
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t19 : ((-229694540197/1250000000000 : ℚ) : ℝ) ≤ stT93 19 := by
  have hc : ((-200243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229694540197/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-200243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c20 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-644103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5676617/10000000) (δ := 673/100000000) (ψ := -127699/1000000) 93 44
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t20 : ((-360092477601/2500000000000 : ℚ) : ℝ) ≤ stT93 20 := by
  have hc : ((-644153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-360092477601/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-644153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c21 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((865351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1312367/10000000) (δ := 589/100000000) (ψ := -127699/1000000) 93 45
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t21 : ((944120402789/5000000000000 : ℚ) : ℝ) ≤ stT93 21 := by
  have hc : ((865301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((944120402789/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((865301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c22 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((138473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3579693/10000000) (δ := 19/4000000) (ψ := -127699/1000000) 93 46
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t22 : ((295118804961/10000000000000 : ℚ) : ℝ) ≤ stT93 22 := by
  have hc : ((138423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295118804961/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((138423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c23 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-904983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3377671/5000000) (δ := 399/50000000) (ψ := -127699/1000000) 93 46
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t23 : ((-377425006957/2000000000000 : ℚ) : ℝ) ≤ stT93 23 := by
  have hc : ((-905033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377425006957/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-905033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c24 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((37191/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942489/10000000) (δ := 167/25000000) (ψ := -127699/1000000) 93 47
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t24 : ((75911711549/400000000000 : ℚ) : ℝ) ≤ stT93 24 := by
  have hc : ((37189/40000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75911711549/400000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((37189/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c25 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-513233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5274361/10000000) (δ := 737/100000000) (ψ := -127699/1000000) 93 48
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t25 : ((-1026566513283/10000000000000 : ℚ) : ℝ) ≤ stT93 25 := by
  have hc : ((-513283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1026566513283/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-513283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c26 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((2063/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 768891/2000000) (δ := 607/100000000) (ψ := -127699/1000000) 93 48
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t26 : ((32317972119/5000000000000 : ℚ) : ℝ) ≤ stT93 26 := by
  have hc : ((16479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32317972119/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((16479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c27 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((328999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1544441/5000000) (δ := 587/100000000) (ψ := -127699/1000000) 93 49
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t27 : ((1266124701/20000000000 : ℚ) : ℝ) ≤ stT93 27 := by
  have hc : ((328949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1266124701/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((328949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c28 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-544541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1073319/2000000) (δ := 219/25000000) (ψ := -127699/1000000) 93 49
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t28 : ((-1029180597393/10000000000000 : ℚ) : ℝ) ≤ stT93 28 := by
  have hc : ((-544591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1029180597393/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-544591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c29 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((642489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -545659/2500000) (δ := 169/25000000) (ψ := -127699/1000000) 93 50
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t29 : ((1192979028367/10000000000000 : ℚ) : ℝ) ≤ stT93 29 := by
  have hc : ((642439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1192979028367/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((642439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c30 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-65107/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227979/400000) (δ := 747/100000000) (ψ := -127699/1000000) 93 50
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t30 : ((-7429857069/62500000000 : ℚ) : ℝ) ≤ stT93 30 := by
  have hc : ((-8139/12500 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7429857069/62500000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-8139/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c31 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((72309/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -476971/2000000) (δ := 37/4000000) (ψ := -127699/1000000) 93 51
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t31 : ((519438284183/5000000000000 : ℚ) : ℝ) ≤ stT93 31 := by
  have hc : ((289211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519438284183/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((289211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c32 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-414953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2498359/5000000) (δ := 183/20000000) (ψ := -127699/1000000) 93 51
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t32 : ((-733628608301/10000000000000 : ℚ) : ℝ) ≤ stT93 32 := by
  have hc : ((-415003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-733628608301/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-415003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c33 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((73761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711367/2000000) (δ := 549/100000000) (ψ := -127699/1000000) 93 52
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t33 : ((2005591549/78125000000 : ℚ) : ℝ) ≤ stT93 33 := by
  have hc : ((9217/62500 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2005591549/78125000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((9217/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c34 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((215501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3383979/10000000) (δ := 181/25000000) (ψ := -127699/1000000) 93 52
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t34 : ((73899046647/2000000000000 : ℚ) : ℝ) ≤ stT93 34 := by
  have hc : ((215451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73899046647/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((215451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c35 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-12309/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2792191/5000000) (δ := 11/2000000) (ψ := -127699/1000000) 93 53
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t35 : ((-2080770379/20000000000 : ℚ) : ℝ) ≤ stT93 35 := by
  have hc : ((-1231/2000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2080770379/20000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-1231/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c36 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((92637/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 965347/10000000) (δ := 593/100000000) (ψ := -127699/1000000) 93 53
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t36 : ((9649162807/62500000000 : ℚ) : ℝ) ≤ stT93 36 := by
  have hc : ((11579/12500 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9649162807/62500000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((11579/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c37 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-48929/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 916951/1250000) (δ := 853/100000000) (ψ := -127699/1000000) 93 53
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t37 : ((-16088579337/100000000000 : ℚ) : ℝ) ≤ stT93 37 := by
  have hc : ((-97863/100000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16088579337/100000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-97863/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c38 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((645747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2171987/10000000) (δ := 11/2000000) (ψ := -127699/1000000) 93 54
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t38 : ((523729356579/5000000000000 : ℚ) : ℝ) ≤ stT93 38 := by
  have hc : ((645697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523729356579/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((645697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c39 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((23869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3867313/10000000) (δ := 533/100000000) (ψ := -127699/1000000) 93 54
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t39 : ((38140912139/10000000000000 : ℚ) : ℝ) ≤ stT93 39 := by
  have hc : ((23819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38140912139/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((23819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c40 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-724913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297713/500000) (δ := 471/100000000) (ψ := -127699/1000000) 93 55
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t40 : ((-1146267272857/10000000000000 : ℚ) : ℝ) ≤ stT93 40 := by
  have hc : ((-724963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1146267272857/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-724963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c41 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((199273/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213227/10000000) (δ := 611/100000000) (ψ := -127699/1000000) 93 55
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t41 : ((311196399831/2000000000000 : ℚ) : ℝ) ≤ stT93 41 := by
  have hc : ((199263/200000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((311196399831/2000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((199263/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c42 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-552187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2694727/5000000) (δ := 381/50000000) (ψ := -127699/1000000) 93 55
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t42 : ((-426060233529/5000000000000 : ℚ) : ℝ) ≤ stT93 42 := by
  have hc : ((-552237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426060233529/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-552237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c43 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-360003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4847669/10000000) (δ := 801/100000000) (ψ := -127699/1000000) 93 56
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t43 : ((-274537892129/5000000000000 : ℚ) : ℝ) ≤ stT93 43 := by
  have hc : ((-360053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274537892129/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-360053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c44 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((980273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248697/5000000) (δ := 631/100000000) (ψ := -127699/1000000) 93 56
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t44 : ((369435266247/2500000000000 : ℚ) : ℝ) ≤ stT93 44 := by
  have hc : ((980223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369435266247/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((980223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c45 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-657983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5722333/10000000) (δ := 411/50000000) (ψ := -127699/1000000) 93 56
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t45 : ((-122617211187/1250000000000 : ℚ) : ℝ) ≤ stT93 45 := by
  have hc : ((-658033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122617211187/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-658033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c46 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-18519/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -975107/2000000) (δ := 431/50000000) (ψ := -127699/1000000) 93 57
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t46 : ((-2730847003/50000000000 : ℚ) : ℝ) ≤ stT93 46 := by
  have hc : ((-37043/100000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2730847003/50000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-37043/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c47 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((998757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 62329/5000000) (δ := 941/100000000) (ψ := -127699/1000000) 93 57
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t47 : ((1456762966843/10000000000000 : ℚ) : ℝ) ≤ stT93 47 := by
  have hc : ((998707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1456762966843/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((998707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c48 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-211627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 627447/1250000) (δ := 841/100000000) (ψ := -127699/1000000) 93 57
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t48 : ((-4773334643/78125000000 : ℚ) : ℝ) ≤ stT93 48 := by
  have hc : ((-52913/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4773334643/78125000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-52913/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c49 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-354107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5894403/10000000) (δ := 903/100000000) (ψ := -127699/1000000) 93 58
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t49 : ((-31618941219/312500000000 : ℚ) : ℝ) ≤ stT93 49 := by
  have hc : ((-88533/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31618941219/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-88533/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c50 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((443749/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -598637/5000000) (δ := 91/10000000) (ψ := -127699/1000000) 93 58
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t50 : ((156880062303/1250000000000 : ℚ) : ℝ) ≤ stT93 50 := by
  have hc : ((110931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156880062303/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((110931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c51 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((51641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3406837/10000000) (δ := 13/2000000) (ψ := -127699/1000000) 93 58
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t51 : ((3614717799/125000000000 : ℚ) : ℝ) ≤ stT93 51 := by
  have hc : ((103257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3614717799/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((103257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c52 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-199927/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7786421/10000000) (δ := 769/100000000) (ψ := -127699/1000000) 93 59
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t52 : ((-277262834687/2000000000000 : ℚ) : ℝ) ≤ stT93 52 := by
  have hc : ((-199937/200000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277262834687/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-199937/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c53 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((225747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -839429/2500000) (δ := 829/100000000) (ψ := -127699/1000000) 93 59
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t53 : ((62003705537/2000000000000 : ℚ) : ℝ) ≤ stT93 53 := by
  have hc : ((225697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62003705537/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((225697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c54 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((115361/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 197641/2000000) (δ := 519/100000000) (ψ := -127699/1000000) 93 59
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t54 : ((627911433513/5000000000000 : ℚ) : ℝ) ≤ stT93 54 := by
  have hc : ((461419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((627911433513/5000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((461419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c55 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-253179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262719/500000) (δ := 49/6250000) (ψ := -127699/1000000) 93 59
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t55 : ((-213387671/3125000000 : ℚ) : ℝ) ≤ stT93 55 := by
  have hc : ((-63301/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213387671/3125000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-63301/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c56 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-804549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6264281/10000000) (δ := 33/4000000) (ψ := -127699/1000000) 93 60
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t56 : ((-1075191275893/10000000000000 : ℚ) : ℝ) ≤ stT93 56 := by
  have hc : ((-804599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1075191275893/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-804599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c57 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((652701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2149129/10000000) (δ := 1/160000) (ψ := -127699/1000000) 93 60
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t57 : ((216114283583/2500000000000 : ℚ) : ℝ) ≤ stT93 57 := by
  have hc : ((652651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216114283583/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((652651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c58 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((726363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1894451/10000000) (δ := 53/6250000) (ψ := -127699/1000000) 93 60
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t58 : ((119211931629/1250000000000 : ℚ) : ℝ) ≤ stT93 58 := by
  have hc : ((726313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119211931629/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((726313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c59 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-700977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5868907/10000000) (δ := 33/6250000) (ψ := -127699/1000000) 93 60
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t59 : ((-91266004103/1000000000000 : ℚ) : ℝ) ≤ stT93 59 := by
  have hc : ((-701027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91266004103/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-701027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c60 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-89823/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2965701/5000000) (δ := 109/20000000) (ψ := -127699/1000000) 93 61
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t60 : ((-92775290083/1000000000000 : ℚ) : ℝ) ≤ stT93 60 := by
  have hc : ((-359317/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92775290083/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-359317/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c61 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((670929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2088339/10000000) (δ := 23/4000000) (ψ := -127699/1000000) 93 61
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t61 : ((53685750217/625000000000 : ℚ) : ℝ) ≤ stT93 61 := by
  have hc : ((670879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53685750217/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((670879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c62 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((779523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 211529/1250000) (δ := 153/20000000) (ψ := -127699/1000000) 93 61
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t62 : ((989931489473/10000000000000 : ℚ) : ℝ) ≤ stT93 62 := by
  have hc : ((779473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((989931489473/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((779473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c63 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-559787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676539/1250000) (δ := 43/6250000) (ψ := -127699/1000000) 93 61
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t63 : ((-352664279617/5000000000000 : ℚ) : ℝ) ≤ stT93 63 := by
  have hc : ((-559837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-352664279617/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-559837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c64 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-441653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6634159/10000000) (δ := 373/50000000) (ψ := -127699/1000000) 93 62
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t64 : ((-276048970839/2500000000000 : ℚ) : ℝ) ≤ stT93 64 := by
  have hc : ((-220839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276048970839/2500000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-220839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c65 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((351359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -605887/2000000) (δ := 323/50000000) (ψ := -127699/1000000) 93 62
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t65 : ((435745064223/10000000000000 : ℚ) : ℝ) ≤ stT93 65 := by
  have hc : ((351309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((435745064223/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((351309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c66 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((39137/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130063/2500000) (δ := 557/100000000) (ψ := -127699/1000000) 93 62
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t66 : ((4817181939/40000000000 : ℚ) : ℝ) ≤ stT93 66 := by
  have hc : ((7827/8000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4817181939/40000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((7827/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c67 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-35819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2008279/5000000) (δ := 787/100000000) (ψ := -127699/1000000) 93 62
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t67 : ((-8764195591/2000000000000 : ℚ) : ℝ) ≤ stT93 67 := by
  have hc : ((-35869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8764195591/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-35869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c68 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-39507/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3730533/5000000) (δ := 897/100000000) (ψ := -127699/1000000) 93 62
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t68 : ((-47911734611/400000000000 : ℚ) : ℝ) ≤ stT93 68 := by
  have hc : ((-39509/40000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47911734611/400000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-39509/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c69 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-361871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4852677/10000000) (δ := 463/50000000) (ψ := -127699/1000000) 93 63
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t69 : ((-435701853139/10000000000000 : ℚ) : ℝ) ≤ stT93 69 := by
  have hc : ((-361921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435701853139/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-361921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c70 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((205921/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -301459/2000000) (δ := 139/25000000) (ψ := -127699/1000000) 93 63
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t70 : ((123053802319/1250000000000 : ℚ) : ℝ) ≤ stT93 70 := by
  have hc : ((411817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123053802319/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((411817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c71 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((754271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1790633/10000000) (δ := 717/100000000) (ψ := -127699/1000000) 93 63
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t71 : ((895095152601/10000000000000 : ℚ) : ℝ) ≤ stT93 71 := by
  have hc : ((754221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((895095152601/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((754221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c72 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-2697/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2521217/5000000) (δ := 383/50000000) (ψ := -127699/1000000) 93 63
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t72 : ((-3178815149/62500000000 : ℚ) : ℝ) ≤ stT93 72 := by
  have hc : ((-43157/100000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3178815149/62500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-43157/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c73 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-987519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3729291/5000000) (δ := 283/50000000) (ψ := -127699/1000000) 93 64
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t73 : ((-288965652107/2500000000000 : ℚ) : ℝ) ≤ stT93 73 := by
  have hc : ((-987569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288965652107/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-987569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c74 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-146779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073817/2500000) (δ := 847/100000000) (ψ := -127699/1000000) 93 64
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t74 : ((-170685335433/10000000000000 : ℚ) : ℝ) ≤ stT93 74 := by
  have hc : ((-146829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170685335433/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-146829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c75 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((445837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73401/625000) (δ := 209/25000000) (ψ := -127699/1000000) 93 64
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t75 : ((1286947791/12500000000 : ℚ) : ℝ) ≤ stT93 75 := by
  have hc : ((111453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1286947791/12500000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((111453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c76 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((723429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1905099/10000000) (δ := 149/25000000) (ψ := -127699/1000000) 93 64
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t76 : ((414886068281/5000000000000 : ℚ) : ℝ) ≤ stT93 76 := by
  have hc : ((723379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414886068281/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((723379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c77 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-395807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2472179/5000000) (δ := 383/50000000) (ψ := -127699/1000000) 93 64
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t77 : ((-225560506171/5000000000000 : ℚ) : ℝ) ≤ stT93 77 := by
  have hc : ((-395857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225560506171/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-395857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c78 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-499673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7763563/10000000) (δ := 139/20000000) (ψ := -127699/1000000) 93 65
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t78 : ((-141449263011/1250000000000 : ℚ) : ℝ) ≤ stT93 78 := by
  have hc : ((-249849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141449263011/1250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-249849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c79 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-85701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -240087/500000) (δ := 19/4000000) (ψ := -127699/1000000) 93 65
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t79 : ((-6027201893/156250000000 : ℚ) : ℝ) ≤ stT93 79 := by
  have hc : ((-171427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6027201893/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-171427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c80 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((91387/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1877173/10000000) (δ := 127/20000000) (ψ := -127699/1000000) 93 65
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t80 : ((408666776259/5000000000000 : ℚ) : ℝ) ≤ stT93 80 := by
  have hc : ((365523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408666776259/5000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((365523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c81 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((919329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1011063/10000000) (δ := 61/12500000) (ψ := -127699/1000000) 93 65
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t81 : ((1021421008969/10000000000000 : ℚ) : ℝ) ≤ stT93 81 := by
  have hc : ((919279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1021421008969/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((919279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c82 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((101/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193193/500000) (δ := 99/20000000) (ψ := -127699/1000000) 93 65
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t82 : ((13914369/5000000000 : ℚ) : ℝ) ≤ stT93 82 := by
  have hc : ((63/2500 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13914369/5000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((63/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c83 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-27879/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1670519/2500000) (δ := 7/800000) (ψ := -127699/1000000) 93 65
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t83 : ((-489646468227/5000000000000 : ℚ) : ℝ) ≤ stT93 83 := by
  have hc : ((-446089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489646468227/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-446089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c84 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-399543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6241423/10000000) (δ := 241/25000000) (ψ := -127699/1000000) 93 66
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t84 : ((-2724779057/31250000000 : ℚ) : ℝ) ≤ stT93 84 := by
  have hc : ((-24973/31250 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2724779057/31250000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-24973/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c85 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((86971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -436239/1250000) (δ := 489/100000000) (ψ := -127699/1000000) 93 66
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t85 : ((11788269099/625000000000 : ℚ) : ℝ) ≤ stT93 85 := by
  have hc : ((43473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11788269099/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((43473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c86 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((952871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -385291/5000000) (δ := 889/100000000) (ψ := -127699/1000000) 93 66
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t86 : ((1027452610467/10000000000000 : ℚ) : ℝ) ≤ stT93 86 := by
  have hc : ((952821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1027452610467/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((952821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c87 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((720049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1917309/10000000) (δ := 387/50000000) (ψ := -127699/1000000) 93 66
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t87 : ((48244972993/625000000000 : ℚ) : ℝ) ≤ stT93 87 := by
  have hc : ((719999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48244972993/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((719999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c88 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-25611/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4574481/10000000) (δ := 201/25000000) (ψ := -127699/1000000) 93 66
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t88 : ((-426668101/15625000000 : ℚ) : ℝ) ≤ stT93 88 := by
  have hc : ((-1601/6250 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426668101/15625000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-1601/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c89 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-966147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7201627/10000000) (δ := 619/100000000) (ψ := -127699/1000000) 93 66
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t89 : ((-512083443803/5000000000000 : ℚ) : ℝ) ≤ stT93 89 := by
  have hc : ((-966197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-512083443803/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-966197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c90 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-178049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92321/156250) (δ := 31/5000000) (ψ := -127699/1000000) 93 67
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t90 : ((-375386761439/5000000000000 : ℚ) : ℝ) ≤ stT93 90 := by
  have hc : ((-356123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375386761439/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-356123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c91 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((29107/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3339457/10000000) (δ := 3/312500) (ψ := -127699/1000000) 93 67
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t91 : ((30505850613/1250000000000 : ℚ) : ℝ) ≤ stT93 91 := by
  have hc : ((116403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30505850613/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((116403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c92 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((949431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49903/625000) (δ := 69/10000000) (ψ := -127699/1000000) 93 67
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t92 : ((247449511983/2500000000000 : ℚ) : ℝ) ≤ stT93 92 := by
  have hc : ((949381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247449511983/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((949381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c93 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((773763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171509/1000000) (δ := 21/2500000) (ψ := -127699/1000000) 93 67
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t93 : ((802302469063/10000000000000 : ℚ) : ℝ) ≤ stT93 93 := by
  have hc : ((773713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((802302469063/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((773713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c94 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-109681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 840349/2000000) (δ := 3/400000) (ψ := -127699/1000000) 93 67
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t94 : ((-56589483741/5000000000000 : ℚ) : ℝ) ≤ stT93 94 := by
  have hc : ((-109731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56589483741/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-109731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c95 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-888487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1332417/2000000) (δ := 41/5000000) (ψ := -127699/1000000) 93 67
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t95 : ((-911620302723/10000000000000 : ℚ) : ℝ) ≤ stT93 95 := by
  have hc : ((-888537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-911620302723/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-888537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c96 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-439491/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6611301/10000000) (δ := 41/5000000) (ψ := -127699/1000000) 93 68
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t96 : ((-112144814859/1250000000000 : ℚ) : ℝ) ≤ stT93 96 := by
  have hc : ((-109879/125000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112144814859/1250000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-109879/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c97 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((-109763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4201953/10000000) (δ := 7/1000000) (ψ := -127699/1000000) 93 68
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t97 : ((-111498300111/10000000000000 : ℚ) : ℝ) ≤ stT93 97 := by
  have hc : ((-109813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111498300111/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-109813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c98 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((747221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -454329/2500000) (δ := 73/10000000) (ψ := -127699/1000000) 93 68
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t98 : ((94344534999/1250000000000 : ℚ) : ℝ) ≤ stT93 98 := by
  have hc : ((747171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94344534999/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((747171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c99 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((195299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54311/1000000) (δ := 483/100000000) (ψ := -127699/1000000) 93 68
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t99 : ((196272670693/2000000000000 : ℚ) : ℝ) ≤ stT93 99 := by
  have hc : ((195289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196272670693/2000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((195289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_c100 :
    |Real.cos (((93 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ))
      - ((406729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2879813/10000000) (δ := 39/5000000) (ψ := -127699/1000000) 93 68
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st93_t100 : ((406678593321/10000000000000 : ℚ) : ℝ) ≤ stT93 100 := by
  have hc : ((406679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((93 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-127699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st93_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((406678593321/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((406679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st93_p1 : ((15497/15625 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT93 (i+1) := by
  rw [Finset.sum_range_one]
  exact st93_t1

theorem st93_p2 : ((1074751324919/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT93 (i+1))
      = (∑ i ∈ Finset.range 1, stT93 (i+1)) + stT93 2 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 1
    simpa using h
  have hprev := st93_p1
  have hstep := st93_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p3 : ((7468361228869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT93 (i+1))
      = (∑ i ∈ Finset.range 2, stT93 (i+1)) + stT93 3 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 2
    simpa using h
  have hprev := st93_p2
  have hstep := st93_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p4 : ((2620810259359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT93 (i+1))
      = (∑ i ∈ Finset.range 3, stT93 (i+1)) + stT93 4 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 3
    simpa using h
  have hprev := st93_p3
  have hstep := st93_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p5 : ((5070574258199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT93 (i+1))
      = (∑ i ∈ Finset.range 4, stT93 (i+1)) + stT93 5 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 4
    simpa using h
  have hprev := st93_p4
  have hstep := st93_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p6 : ((44875295643/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT93 (i+1))
      = (∑ i ∈ Finset.range 5, stT93 (i+1)) + stT93 6 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 5
    simpa using h
  have hprev := st93_p5
  have hstep := st93_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p7 : ((2785299935831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT93 (i+1))
      = (∑ i ∈ Finset.range 6, stT93 (i+1)) + stT93 7 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 6
    simpa using h
  have hprev := st93_p6
  have hstep := st93_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p8 : ((3856304805389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT93 (i+1))
      = (∑ i ∈ Finset.range 7, stT93 (i+1)) + stT93 8 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 7
    simpa using h
  have hprev := st93_p7
  have hstep := st93_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p9 : ((640090828813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT93 (i+1))
      = (∑ i ∈ Finset.range 8, stT93 (i+1)) + stT93 9 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 8
    simpa using h
  have hprev := st93_p8
  have hstep := st93_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p10 : ((3176736622579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT93 (i+1))
      = (∑ i ∈ Finset.range 9, stT93 (i+1)) + stT93 10 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 9
    simpa using h
  have hprev := st93_p9
  have hstep := st93_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p11 : ((34169171261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT93 (i+1))
      = (∑ i ∈ Finset.range 10, stT93 (i+1)) + stT93 11 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 10
    simpa using h
  have hprev := st93_p10
  have hstep := st93_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p12 : ((535217705091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT93 (i+1))
      = (∑ i ∈ Finset.range 11, stT93 (i+1)) + stT93 12 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 11
    simpa using h
  have hprev := st93_p11
  have hstep := st93_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p13 : ((1915899287091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT93 (i+1))
      = (∑ i ∈ Finset.range 12, stT93 (i+1)) + stT93 13 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 12
    simpa using h
  have hprev := st93_p12
  have hstep := st93_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p14 : ((3078281052273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT93 (i+1))
      = (∑ i ∈ Finset.range 13, stT93 (i+1)) + stT93 14 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 13
    simpa using h
  have hprev := st93_p13
  have hstep := st93_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p15 : ((4106772078277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT93 (i+1))
      = (∑ i ∈ Finset.range 14, stT93 (i+1)) + stT93 15 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 14
    simpa using h
  have hprev := st93_p14
  have hstep := st93_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p16 : ((5273087078277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT93 (i+1))
      = (∑ i ∈ Finset.range 15, stT93 (i+1)) + stT93 16 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 15
    simpa using h
  have hprev := st93_p15
  have hstep := st93_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p17 : ((6439397122269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT93 (i+1))
      = (∑ i ∈ Finset.range 16, stT93 (i+1)) + stT93 17 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 16
    simpa using h
  have hprev := st93_p16
  have hstep := st93_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p18 : ((2662841943/1953125000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT93 (i+1))
      = (∑ i ∈ Finset.range 17, stT93 (i+1)) + stT93 18 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 17
    simpa using h
  have hprev := st93_p17
  have hstep := st93_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p19 : ((1474524303323/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT93 (i+1))
      = (∑ i ∈ Finset.range 18, stT93 (i+1)) + stT93 19 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 18
    simpa using h
  have hprev := st93_p18
  have hstep := st93_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p20 : ((517791225809/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT93 (i+1))
      = (∑ i ∈ Finset.range 19, stT93 (i+1)) + stT93 20 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 19
    simpa using h
  have hprev := st93_p19
  have hstep := st93_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p21 : ((6122032660879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT93 (i+1))
      = (∑ i ∈ Finset.range 20, stT93 (i+1)) + stT93 21 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 20
    simpa using h
  have hprev := st93_p20
  have hstep := st93_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p22 : ((12539184126719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT93 (i+1))
      = (∑ i ∈ Finset.range 21, stT93 (i+1)) + stT93 22 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 21
    simpa using h
  have hprev := st93_p21
  have hstep := st93_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p23 : ((5326029545967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT93 (i+1))
      = (∑ i ∈ Finset.range 22, stT93 (i+1)) + stT93 23 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 22
    simpa using h
  have hprev := st93_p22
  have hstep := st93_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p24 : ((12549851880659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT93 (i+1))
      = (∑ i ∈ Finset.range 23, stT93 (i+1)) + stT93 24 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 23
    simpa using h
  have hprev := st93_p23
  have hstep := st93_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p25 : ((720205335461/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT93 (i+1))
      = (∑ i ∈ Finset.range 24, stT93 (i+1)) + stT93 25 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 24
    simpa using h
  have hprev := st93_p24
  have hstep := st93_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p26 : ((5793960655807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT93 (i+1))
      = (∑ i ∈ Finset.range 25, stT93 (i+1)) + stT93 26 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 25
    simpa using h
  have hprev := st93_p25
  have hstep := st93_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p27 : ((6110491831057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT93 (i+1))
      = (∑ i ∈ Finset.range 26, stT93 (i+1)) + stT93 27 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 26
    simpa using h
  have hprev := st93_p26
  have hstep := st93_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p28 : ((11191803064721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT93 (i+1))
      = (∑ i ∈ Finset.range 27, stT93 (i+1)) + stT93 28 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 27
    simpa using h
  have hprev := st93_p27
  have hstep := st93_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p29 : ((387024440409/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT93 (i+1))
      = (∑ i ∈ Finset.range 28, stT93 (i+1)) + stT93 29 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 28
    simpa using h
  have hprev := st93_p28
  have hstep := st93_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p30 : ((43734394383/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT93 (i+1))
      = (∑ i ∈ Finset.range 29, stT93 (i+1)) + stT93 30 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 29
    simpa using h
  have hprev := st93_p29
  have hstep := st93_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p31 : ((6117440765207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT93 (i+1))
      = (∑ i ∈ Finset.range 30, stT93 (i+1)) + stT93 31 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 30
    simpa using h
  have hprev := st93_p30
  have hstep := st93_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p32 : ((11501252922113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT93 (i+1))
      = (∑ i ∈ Finset.range 31, stT93 (i+1)) + stT93 32 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 31
    simpa using h
  have hprev := st93_p31
  have hstep := st93_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p33 : ((2351593728077/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT93 (i+1))
      = (∑ i ∈ Finset.range 32, stT93 (i+1)) + stT93 33 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 32
    simpa using h
  have hprev := st93_p32
  have hstep := st93_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p34 : ((606373193681/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT93 (i+1))
      = (∑ i ∈ Finset.range 33, stT93 (i+1)) + stT93 34 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 33
    simpa using h
  have hprev := st93_p33
  have hstep := st93_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p35 : ((277176967103/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT93 (i+1))
      = (∑ i ∈ Finset.range 34, stT93 (i+1)) + stT93 35 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 34
    simpa using h
  have hprev := st93_p34
  have hstep := st93_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p36 : ((315773618331/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT93 (i+1))
      = (∑ i ∈ Finset.range 35, stT93 (i+1)) + stT93 36 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 35
    simpa using h
  have hprev := st93_p35
  have hstep := st93_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p37 : ((551104339977/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT93 (i+1))
      = (∑ i ∈ Finset.range 36, stT93 (i+1)) + stT93 37 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 36
    simpa using h
  have hprev := st93_p36
  have hstep := st93_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p38 : ((6034772756349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT93 (i+1))
      = (∑ i ∈ Finset.range 37, stT93 (i+1)) + stT93 38 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 37
    simpa using h
  have hprev := st93_p37
  have hstep := st93_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p39 : ((12107686424837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT93 (i+1))
      = (∑ i ∈ Finset.range 38, stT93 (i+1)) + stT93 39 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 38
    simpa using h
  have hprev := st93_p38
  have hstep := st93_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p40 : ((548070957599/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT93 (i+1))
      = (∑ i ∈ Finset.range 39, stT93 (i+1)) + stT93 40 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 39
    simpa using h
  have hprev := st93_p39
  have hstep := st93_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p41 : ((2503480230227/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT93 (i+1))
      = (∑ i ∈ Finset.range 40, stT93 (i+1)) + stT93 41 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 40
    simpa using h
  have hprev := st93_p40
  have hstep := st93_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p42 : ((11665280684077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT93 (i+1))
      = (∑ i ∈ Finset.range 41, stT93 (i+1)) + stT93 42 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 41
    simpa using h
  have hprev := st93_p41
  have hstep := st93_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p43 : ((11116204899819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT93 (i+1))
      = (∑ i ∈ Finset.range 42, stT93 (i+1)) + stT93 43 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 42
    simpa using h
  have hprev := st93_p42
  have hstep := st93_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p44 : ((12593945964807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT93 (i+1))
      = (∑ i ∈ Finset.range 43, stT93 (i+1)) + stT93 44 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 43
    simpa using h
  have hprev := st93_p43
  have hstep := st93_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p45 : ((11613008275311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT93 (i+1))
      = (∑ i ∈ Finset.range 44, stT93 (i+1)) + stT93 45 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 44
    simpa using h
  have hprev := st93_p44
  have hstep := st93_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p46 : ((11066838874711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT93 (i+1))
      = (∑ i ∈ Finset.range 45, stT93 (i+1)) + stT93 46 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 45
    simpa using h
  have hprev := st93_p45
  have hstep := st93_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p47 : ((6261800920777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT93 (i+1))
      = (∑ i ∈ Finset.range 46, stT93 (i+1)) + stT93 47 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 46
    simpa using h
  have hprev := st93_p46
  have hstep := st93_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p48 : ((47650460029/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT93 (i+1))
      = (∑ i ∈ Finset.range 47, stT93 (i+1)) + stT93 48 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 47
    simpa using h
  have hprev := st93_p47
  have hstep := st93_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p49 : ((5450404444121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT93 (i+1))
      = (∑ i ∈ Finset.range 48, stT93 (i+1)) + stT93 49 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 48
    simpa using h
  have hprev := st93_p48
  have hstep := st93_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p50 : ((6077924693333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT93 (i+1))
      = (∑ i ∈ Finset.range 49, stT93 (i+1)) + stT93 50 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 49
    simpa using h
  have hprev := st93_p49
  have hstep := st93_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p51 : ((6222513405293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT93 (i+1))
      = (∑ i ∈ Finset.range 50, stT93 (i+1)) + stT93 51 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 50
    simpa using h
  have hprev := st93_p50
  have hstep := st93_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p52 : ((11058712637151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT93 (i+1))
      = (∑ i ∈ Finset.range 51, stT93 (i+1)) + stT93 52 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 51
    simpa using h
  have hprev := st93_p51
  have hstep := st93_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p53 : ((2842182791209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT93 (i+1))
      = (∑ i ∈ Finset.range 52, stT93 (i+1)) + stT93 53 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 52
    simpa using h
  have hprev := st93_p52
  have hstep := st93_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p54 : ((6312277015931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT93 (i+1))
      = (∑ i ∈ Finset.range 53, stT93 (i+1)) + stT93 54 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 53
    simpa using h
  have hprev := st93_p53
  have hstep := st93_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p55 : ((5970856742331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT93 (i+1))
      = (∑ i ∈ Finset.range 54, stT93 (i+1)) + stT93 55 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 54
    simpa using h
  have hprev := st93_p54
  have hstep := st93_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p56 : ((10866522208769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT93 (i+1))
      = (∑ i ∈ Finset.range 55, stT93 (i+1)) + stT93 56 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 55
    simpa using h
  have hprev := st93_p55
  have hstep := st93_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p57 : ((11730979343101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT93 (i+1))
      = (∑ i ∈ Finset.range 56, stT93 (i+1)) + stT93 57 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 56
    simpa using h
  have hprev := st93_p56
  have hstep := st93_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p58 : ((12684674796133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT93 (i+1))
      = (∑ i ∈ Finset.range 57, stT93 (i+1)) + stT93 58 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 57
    simpa using h
  have hprev := st93_p57
  have hstep := st93_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p59 : ((11772014755103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT93 (i+1))
      = (∑ i ∈ Finset.range 58, stT93 (i+1)) + stT93 59 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 58
    simpa using h
  have hprev := st93_p58
  have hstep := st93_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p60 : ((10844261854273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT93 (i+1))
      = (∑ i ∈ Finset.range 59, stT93 (i+1)) + stT93 60 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 59
    simpa using h
  have hprev := st93_p59
  have hstep := st93_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p61 : ((2340646771549/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT93 (i+1))
      = (∑ i ∈ Finset.range 60, stT93 (i+1)) + stT93 61 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 60
    simpa using h
  have hprev := st93_p60
  have hstep := st93_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p62 : ((6346582673609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT93 (i+1))
      = (∑ i ∈ Finset.range 61, stT93 (i+1)) + stT93 62 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 61
    simpa using h
  have hprev := st93_p61
  have hstep := st93_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p63 : ((749239799249/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT93 (i+1))
      = (∑ i ∈ Finset.range 62, stT93 (i+1)) + stT93 63 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 62
    simpa using h
  have hprev := st93_p62
  have hstep := st93_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p64 : ((2720910226157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT93 (i+1))
      = (∑ i ∈ Finset.range 63, stT93 (i+1)) + stT93 64 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 63
    simpa using h
  have hprev := st93_p63
  have hstep := st93_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p65 : ((11319385968851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT93 (i+1))
      = (∑ i ∈ Finset.range 64, stT93 (i+1)) + stT93 65 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 64
    simpa using h
  have hprev := st93_p64
  have hstep := st93_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p66 : ((12523681453601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT93 (i+1))
      = (∑ i ∈ Finset.range 65, stT93 (i+1)) + stT93 66 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 65
    simpa using h
  have hprev := st93_p65
  have hstep := st93_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p67 : ((6239930237823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT93 (i+1))
      = (∑ i ∈ Finset.range 66, stT93 (i+1)) + stT93 67 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 66
    simpa using h
  have hprev := st93_p66
  have hstep := st93_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p68 : ((11282067110371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT93 (i+1))
      = (∑ i ∈ Finset.range 67, stT93 (i+1)) + stT93 68 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 67
    simpa using h
  have hprev := st93_p67
  have hstep := st93_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p69 : ((677897828577/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT93 (i+1))
      = (∑ i ∈ Finset.range 68, stT93 (i+1)) + stT93 69 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 68
    simpa using h
  have hprev := st93_p68
  have hstep := st93_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p70 : ((1478849459473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT93 (i+1))
      = (∑ i ∈ Finset.range 69, stT93 (i+1)) + stT93 70 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 69
    simpa using h
  have hprev := st93_p69
  have hstep := st93_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p71 : ((2545178165677/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT93 (i+1))
      = (∑ i ∈ Finset.range 70, stT93 (i+1)) + stT93 71 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 70
    simpa using h
  have hprev := st93_p70
  have hstep := st93_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p72 : ((2443456080909/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT93 (i+1))
      = (∑ i ∈ Finset.range 71, stT93 (i+1)) + stT93 72 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 71
    simpa using h
  have hprev := st93_p71
  have hstep := st93_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p73 : ((11061417796117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT93 (i+1))
      = (∑ i ∈ Finset.range 72, stT93 (i+1)) + stT93 73 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 72
    simpa using h
  have hprev := st93_p72
  have hstep := st93_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p74 : ((2722683115171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT93 (i+1))
      = (∑ i ∈ Finset.range 73, stT93 (i+1)) + stT93 74 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 73
    simpa using h
  have hprev := st93_p73
  have hstep := st93_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p75 : ((2980072673371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT93 (i+1))
      = (∑ i ∈ Finset.range 74, stT93 (i+1)) + stT93 75 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 74
    simpa using h
  have hprev := st93_p74
  have hstep := st93_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p76 : ((6375031415023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT93 (i+1))
      = (∑ i ∈ Finset.range 75, stT93 (i+1)) + stT93 76 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 75
    simpa using h
  have hprev := st93_p75
  have hstep := st93_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p77 : ((1537367727213/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT93 (i+1))
      = (∑ i ∈ Finset.range 76, stT93 (i+1)) + stT93 77 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 76
    simpa using h
  have hprev := st93_p76
  have hstep := st93_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p78 : ((697959232101/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT93 (i+1))
      = (∑ i ∈ Finset.range 77, stT93 (i+1)) + stT93 78 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 77
    simpa using h
  have hprev := st93_p77
  have hstep := st93_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p79 : ((673850424529/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT93 (i+1))
      = (∑ i ∈ Finset.range 78, stT93 (i+1)) + stT93 79 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 78
    simpa using h
  have hprev := st93_p78
  have hstep := st93_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p80 : ((5799470172491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT93 (i+1))
      = (∑ i ∈ Finset.range 79, stT93 (i+1)) + stT93 80 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 79
    simpa using h
  have hprev := st93_p79
  have hstep := st93_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p81 : ((12620361353951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT93 (i+1))
      = (∑ i ∈ Finset.range 80, stT93 (i+1)) + stT93 81 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 80
    simpa using h
  have hprev := st93_p80
  have hstep := st93_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p82 : ((12648190091951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT93 (i+1))
      = (∑ i ∈ Finset.range 81, stT93 (i+1)) + stT93 82 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 81
    simpa using h
  have hprev := st93_p81
  have hstep := st93_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p83 : ((11668897155497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT93 (i+1))
      = (∑ i ∈ Finset.range 82, stT93 (i+1)) + stT93 83 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 82
    simpa using h
  have hprev := st93_p82
  have hstep := st93_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p84 : ((10796967857257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT93 (i+1))
      = (∑ i ∈ Finset.range 83, stT93 (i+1)) + stT93 84 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 83
    simpa using h
  have hprev := st93_p83
  have hstep := st93_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p85 : ((10985580162841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT93 (i+1))
      = (∑ i ∈ Finset.range 84, stT93 (i+1)) + stT93 85 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 84
    simpa using h
  have hprev := st93_p84
  have hstep := st93_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p86 : ((3003258193327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT93 (i+1))
      = (∑ i ∈ Finset.range 85, stT93 (i+1)) + stT93 86 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 85
    simpa using h
  have hprev := st93_p85
  have hstep := st93_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p87 : ((3196238085299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT93 (i+1))
      = (∑ i ∈ Finset.range 86, stT93 (i+1)) + stT93 87 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 86
    simpa using h
  have hprev := st93_p86
  have hstep := st93_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p88 : ((3127971189139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT93 (i+1))
      = (∑ i ∈ Finset.range 87, stT93 (i+1)) + stT93 88 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 87
    simpa using h
  have hprev := st93_p87
  have hstep := st93_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p89 : ((229754357379/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT93 (i+1))
      = (∑ i ∈ Finset.range 88, stT93 (i+1)) + stT93 89 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 88
    simpa using h
  have hprev := st93_p88
  have hstep := st93_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p90 : ((1342118043259/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT93 (i+1))
      = (∑ i ∈ Finset.range 89, stT93 (i+1)) + stT93 90 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 89
    simpa using h
  have hprev := st93_p89
  have hstep := st93_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p91 : ((85788993367/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT93 (i+1))
      = (∑ i ∈ Finset.range 90, stT93 (i+1)) + stT93 91 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 90
    simpa using h
  have hprev := st93_p90
  have hstep := st93_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p92 : ((2992697299727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT93 (i+1))
      = (∑ i ∈ Finset.range 91, stT93 (i+1)) + stT93 92 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 91
    simpa using h
  have hprev := st93_p91
  have hstep := st93_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p93 : ((12773091667971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT93 (i+1))
      = (∑ i ∈ Finset.range 92, stT93 (i+1)) + stT93 93 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 92
    simpa using h
  have hprev := st93_p92
  have hstep := st93_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p94 : ((12659912700489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT93 (i+1))
      = (∑ i ∈ Finset.range 93, stT93 (i+1)) + stT93 94 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 93
    simpa using h
  have hprev := st93_p93
  have hstep := st93_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p95 : ((5874146198883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT93 (i+1))
      = (∑ i ∈ Finset.range 94, stT93 (i+1)) + stT93 95 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 94
    simpa using h
  have hprev := st93_p94
  have hstep := st93_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p96 : ((5425566939447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT93 (i+1))
      = (∑ i ∈ Finset.range 95, stT93 (i+1)) + stT93 96 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 95
    simpa using h
  have hprev := st93_p95
  have hstep := st93_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p97 : ((10739635578783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT93 (i+1))
      = (∑ i ∈ Finset.range 96, stT93 (i+1)) + stT93 97 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 96
    simpa using h
  have hprev := st93_p96
  have hstep := st93_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p98 : ((459775674351/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT93 (i+1))
      = (∑ i ∈ Finset.range 97, stT93 (i+1)) + stT93 98 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 97
    simpa using h
  have hprev := st93_p97
  have hstep := st93_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p99 : ((155946940153/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT93 (i+1))
      = (∑ i ∈ Finset.range 98, stT93 (i+1)) + stT93 99 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 98
    simpa using h
  have hprev := st93_p98
  have hstep := st93_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st93_p100 : ((12882433805561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT93 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT93 (i+1))
      = (∑ i ∈ Finset.range 99, stT93 (i+1)) + stT93 100 := by
    have h := Finset.sum_range_succ (fun i => stT93 (i+1)) 99
    simpa using h
  have hprev := st93_p99
  have hstep := st93_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 93`.** -/
theorem station_93_sign : hardyG (((93:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 93 100 (by norm_num) (by norm_num)
    ((-127699/1000000 : ℚ) : ℝ)
  have hchain := st93_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT93 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((93:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-127699/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((93:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((93:ℕ)):ℝ)+1) * ((((93:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2263883/2480000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12882433805561/10000000000000 : ℚ) : ℝ) - ((2263883/2480000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-127699/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((93:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-127699/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((93:ℕ)):ℝ))).re
      - Real.sin ((-127699/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((93:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((93:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((93:ℕ)):ℝ)
      = ((((93:ℕ)):ℝ) * (Real.log (((93:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((93:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_93
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
  have hθwin : |(((-127699/1000000 : ℚ) : ℝ) + ((13:ℤ)) * (2*Real.pi) - Real.pi) - theta (((93:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((93:ℕ)):ℝ))
    (φ := ((-127699/1000000 : ℚ) : ℝ) + ((13:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-127699/1000000 : ℚ) : ℝ) + ((13:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-127699/1000000 : ℚ)) : ℝ) - Real.pi) + ((13:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-127699/1000000 : ℚ)) : ℝ) - Real.pi) 13).1,
    (cos_sin_shift ((((-127699/1000000 : ℚ)) : ℝ) - Real.pi) 13).2]
  exact cos_sin_flip ((-127699/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_93_sign
end AxiomAudit
