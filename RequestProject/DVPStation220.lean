import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 220` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT220 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((220 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))

theorem st220_c1 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((407249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359799/1250000) (δ := 201/1000000000) (ψ := 1151357/1000000) 220 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t1 : ((407199/1000000 : ℚ) : ℝ) ≤ stT220 1 := by
  have hc : ((407199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407199/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((407199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c2 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((855351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680711/5000000) (δ := 5587/500000000) (ψ := 1151357/1000000) 220 24
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t2 : ((6047890676167/10000000000000 : ℚ) : ℝ) ≤ stT220 2 := by
  have hc : ((855301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6047890676167/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((855301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c3 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-209927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4455741/10000000) (δ := 5537/500000000) (ψ := 1151357/1000000) 220 38
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t3 : ((-1212302839431/10000000000000 : ℚ) : ℝ) ≤ stT220 3 := by
  have hc : ((-209977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1212302839431/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-209977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c4 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-310379/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5601263/10000000) (δ := 11057/1000000000) (ψ := 1151357/1000000) 220 48
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t4 : ((-388005077601/1250000000000 : ℚ) : ℝ) ≤ stT220 4 := by
  have hc : ((-77601/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388005077601/1250000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-77601/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c5 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((483091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2666537/10000000) (δ := 2751/250000000) (ψ := 1151357/1000000) 220 56
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t5 : ((432044912507/2000000000000 : ℚ) : ℝ) ≤ stT220 5 := by
  have hc : ((483041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432044912507/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((483041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c6 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-94387/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7012381/10000000) (δ := 11049/1000000000) (ψ := 1151357/1000000) 220 63
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t6 : ((-48169216917/125000000000 : ℚ) : ℝ) ≤ stT220 6 := by
  have hc : ((-11799/12500 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48169216917/125000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-11799/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c7 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((38121/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24041/312500) (δ := 1109/100000000) (ψ := 1151357/1000000) 220 68
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t7 : ((36019062409/100000000000 : ℚ) : ℝ) ≤ stT220 7 := by
  have hc : ((38119/40000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36019062409/100000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((38119/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c8 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-700393/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5866859/10000000) (δ := 11177/1000000000) (ψ := 1151357/1000000) 220 73
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t8 : ((-1238220020781/5000000000000 : ℚ) : ℝ) ≤ stT220 8 := by
  have hc : ((-700443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1238220020781/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-700443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c9 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((893/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1959031/5000000) (δ := 11149/1000000000) (ψ := 1151357/1000000) 220 77
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t9 : ((5869999413/5000000000000 : ℚ) : ℝ) ≤ stT220 9 := by
  have hc : ((1761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5869999413/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((1761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c10 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-232253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726581/2500000) (δ := 1397/125000000) (ψ := 1151357/1000000) 220 80
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t10 : ((-734488080809/2500000000000 : ℚ) : ℝ) ≤ stT220 10 := by
  have hc : ((-464531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-734488080809/2500000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-464531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c11 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((168027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87623/250000) (δ := 5599/500000000) (ψ := 1151357/1000000) 220 84
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t11 : ((506469636401/10000000000000 : ℚ) : ℝ) ≤ stT220 11 := by
  have hc : ((167977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((506469636401/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((167977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c12 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((445543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2772539/10000000) (δ := 5563/500000000) (ψ := 1151357/1000000) 220 87
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t12 : ((1286027363243/10000000000000 : ℚ) : ℝ) ≤ stT220 12 := by
  have hc : ((445493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1286027363243/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((445493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c13 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-43883/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367059/625000) (δ := 1381/125000000) (ψ := 1151357/1000000) 220 90
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t13 : ((-973745692589/5000000000000 : ℚ) : ℝ) ≤ stT220 13 := by
  have hc : ((-351089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-973745692589/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-351089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c14 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((45393/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3470529/10000000) (δ := 11141/1000000000) (ψ := 1151357/1000000) 220 92
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t14 : ((60642234433/1250000000000 : ℚ) : ℝ) ≤ stT220 14 := by
  have hc : ((90761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60642234433/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((90761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c15 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-81679/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1141453/2000000) (δ := 699/62500000) (ψ := 1151357/1000000) 220 95
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t15 : ((-843641667849/5000000000000 : ℚ) : ℝ) ≤ stT220 15 := by
  have hc : ((-326741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-843641667849/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-326741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c16 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((159119/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1627017/10000000) (δ := 2201/200000000) (ψ := 1151357/1000000) 220 97
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t16 : ((159109/800000 : ℚ) : ℝ) ≤ stT220 16 := by
  have hc : ((159109/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159109/800000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((159109/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c17 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((992781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150293/5000000) (δ := 11191/1000000000) (ψ := 1151357/1000000) 220 99
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t17 : ((601931521809/2500000000000 : ℚ) : ℝ) ≤ stT220 17 := by
  have hc : ((992731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601931521809/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((992731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c18 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((61983/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16089/500000) (δ := 11027/1000000000) (ψ := 1151357/1000000) 220 101
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t18 : ((584351715729/2500000000000 : ℚ) : ℝ) ≤ stT220 18 := by
  have hc : ((495839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584351715729/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((495839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c19 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((856227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357187/10000000) (δ := 5581/500000000) (ψ := 1151357/1000000) 220 103
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t19 : ((1964204457789/10000000000000 : ℚ) : ℝ) ≤ stT220 19 := by
  have hc : ((856177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1964204457789/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((856177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c20 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-251203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2280899/5000000) (δ := 2211/200000000) (ψ := 1151357/1000000) 220 105
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t20 : ((-140454698301/2500000000000 : ℚ) : ℝ) ≤ stT220 20 := by
  have hc : ((-251253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140454698301/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-251253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c21 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-869971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6564849/10000000) (δ := 11163/1000000000) (ψ := 1151357/1000000) 220 106
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t21 : ((-1898541555759/10000000000000 : ℚ) : ℝ) ≤ stT220 21 := by
  have hc : ((-870021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1898541555759/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-870021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c22 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((957101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 367461/5000000) (δ := 5513/500000000) (ψ := 1151357/1000000) 220 108
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t22 : ((2040439431357/10000000000000 : ℚ) : ℝ) ≤ stT220 22 := by
  have hc : ((957051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2040439431357/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((957051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c23 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-398469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3116257/5000000) (δ := 11191/1000000000) (ψ := 1151357/1000000) 220 110
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t23 : ((-83091777163/500000000000 : ℚ) : ℝ) ≤ stT220 23 := by
  have hc : ((-199247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83091777163/500000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-199247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c24 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((16653/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 733651/5000000) (δ := 2221/200000000) (ψ := 1151357/1000000) 220 111
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t24 : ((8497686283/50000000000 : ℚ) : ℝ) ≤ stT220 24 := by
  have hc : ((4163/5000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8497686283/50000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((4163/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c25 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-197959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1874131/2500000) (δ := 11113/1000000000) (ψ := 1151357/1000000) 220 113
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t25 : ((-395938197969/2000000000000 : ℚ) : ℝ) ≤ stT220 25 := by
  have hc : ((-197969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395938197969/2000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-197969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c26 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((397059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1633103/10000000) (δ := 11183/1000000000) (ψ := 1151357/1000000) 220 114
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t26 : ((389323798237/2500000000000 : ℚ) : ℝ) ≤ stT220 26 := by
  have hc : ((198517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389323798237/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((198517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c27 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((202937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3416099/10000000) (δ := 2769/250000000) (ψ := 1151357/1000000) 220 115
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t27 : ((780912063/20000000000 : ℚ) : ℝ) ≤ stT220 27 := by
  have hc : ((202887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((780912063/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((202887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c28 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-998351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7710371/10000000) (δ := 5517/500000000) (ψ := 1151357/1000000) 220 116
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t28 : ((-1886801173023/10000000000000 : ℚ) : ℝ) ≤ stT220 28 := by
  have hc : ((-998401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1886801173023/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-998401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c29 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-7607/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4405341/10000000) (δ := 5577/500000000) (ψ := 1151357/1000000) 220 118
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t29 : ((-7064781493/200000000000 : ℚ) : ℝ) ≤ stT220 29 := by
  have hc : ((-7609/40000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7064781493/200000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-7609/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c30 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((832611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1467479/10000000) (δ := 11047/1000000000) (ψ := 1151357/1000000) 220 119
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t30 : ((1520040752701/10000000000000 : ℚ) : ℝ) ≤ stT220 30 := by
  have hc : ((832561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1520040752701/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((832561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c31 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((235387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 859003/10000000) (δ := 11063/1000000000) (ψ := 1151357/1000000) 220 120
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t31 : ((845490153697/5000000000000 : ℚ) : ℝ) ≤ stT220 31 := by
  have hc : ((470749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((845490153697/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((470749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c32 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((501789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104513/400000) (δ := 1117/100000000) (ψ := 1151357/1000000) 220 121
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t32 : ((443478572537/5000000000000 : ℚ) : ℝ) ≤ stT220 32 := by
  have hc : ((501739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((443478572537/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((501739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c33 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((3909/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3829241/10000000) (δ := 5563/500000000) (ψ := 1151357/1000000) 220 122
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t33 : ((13273417/1953125000 : ℚ) : ℝ) ≤ stT220 33 := by
  have hc : ((122/3125 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13273417/1953125000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((122/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c34 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-6073/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1135107/2500000) (δ := 5509/500000000) (ψ := 1151357/1000000) 220 123
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t34 : ((-20834507421/500000000000 : ℚ) : ℝ) ≤ stT220 34 := by
  have hc : ((-24297/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20834507421/500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-24297/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c35 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-332959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 477559/1000000) (δ := 2773/250000000) (ψ := 1151357/1000000) 220 124
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t35 : ((-562888109781/10000000000000 : ℚ) : ℝ) ≤ stT220 35 := by
  have hc : ((-333009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562888109781/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-333009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c36 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-50227/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2280811/5000000) (δ := 11199/1000000000) (ψ := 1151357/1000000) 220 125
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t36 : ((-83728350079/2000000000000 : ℚ) : ℝ) ≤ stT220 36 := by
  have hc : ((-50237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83728350079/2000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-50237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c37 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((1553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 980777/2500000) (δ := 11097/1000000000) (ψ := 1151357/1000000) 220 126
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t37 : ((2470915467/10000000000000 : ℚ) : ℝ) ≤ stT220 37 := by
  have hc : ((1503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2470915467/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((1503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c38 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((405691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 576531/2000000) (δ := 11013/1000000000) (ψ := 1151357/1000000) 220 127
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t38 : ((329018254587/5000000000000 : ℚ) : ℝ) ≤ stT220 38 := by
  have hc : ((405641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329018254587/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((405641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c39 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((166799/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1461217/10000000) (δ := 139/12500000) (ψ := 1151357/1000000) 220 128
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t39 : ((267076056709/2000000000000 : ℚ) : ℝ) ≤ stT220 39 := by
  have hc : ((166789/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267076056709/2000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((166789/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c40 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((991719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -321957/10000000) (δ := 447/40000000) (ψ := 1151357/1000000) 220 129
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t40 : ((783982769661/5000000000000 : ℚ) : ℝ) ≤ stT220 40 := by
  have hc : ((991669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((783982769661/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((991669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c41 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((278679/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244899/1000000) (δ := 2767/250000000) (ψ := 1151357/1000000) 220 130
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t41 : ((217592130999/2500000000000 : ℚ) : ℝ) ≤ stT220 41 := by
  have hc : ((139327/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217592130999/2500000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((139327/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c42 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-380663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4903273/10000000) (δ := 5521/500000000) (ψ := 1151357/1000000) 220 131
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t42 : ((-293726551621/5000000000000 : ℚ) : ℝ) ≤ stT220 42 := by
  have hc : ((-380713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293726551621/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-380713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c43 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-997277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7669461/10000000) (δ := 11149/1000000000) (ψ := 1151357/1000000) 220 132
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t43 : ((-760454856211/5000000000000 : ℚ) : ℝ) ≤ stT220 43 := by
  have hc : ((-997327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-760454856211/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-997327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c44 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-406947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1243691/2500000) (δ := 11149/1000000000) (ψ := 1151357/1000000) 220 132
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t44 : ((-613571176329/10000000000000 : ℚ) : ℝ) ≤ stT220 44 := by
  have hc : ((-406997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-613571176329/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-406997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c45 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((397819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40671/250000) (δ := 11147/1000000000) (ψ := 1151357/1000000) 220 133
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t45 : ((296497945767/2500000000000 : ℚ) : ℝ) ≤ stT220 45 := by
  have hc : ((198897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296497945767/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((198897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c46 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((69879/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249091/1250000) (δ := 11039/1000000000) (ψ := 1151357/1000000) 220 134
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t46 : ((51511776603/500000000000 : ℚ) : ℝ) ≤ stT220 46 := by
  have hc : ((34937/50000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51511776603/500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((34937/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c47 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-701923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2936113/5000000) (δ := 11071/1000000000) (ψ := 1151357/1000000) 220 135
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t47 : ((-20478658329/200000000000 : ℚ) : ℝ) ≤ stT220 47 := by
  have hc : ((-701973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20478658329/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-701973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c48 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-163349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 713393/1250000) (δ := 11071/1000000000) (ψ := 1151357/1000000) 220 135
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t48 : ((-29474008553/312500000000 : ℚ) : ℝ) ≤ stT220 48 := by
  have hc : ((-326723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29474008553/312500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-326723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c49 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((859811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1339741/10000000) (δ := 5589/500000000) (ψ := 1151357/1000000) 220 136
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t49 : ((1228229631531/10000000000000 : ℚ) : ℝ) ≤ stT220 49 := by
  have hc : ((859761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1228229631531/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((859761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c50 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((132461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3256683/10000000) (δ := 5559/500000000) (ψ := 1151357/1000000) 220 137
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t50 : ((46823178217/1250000000000 : ℚ) : ℝ) ≤ stT220 50 := by
  have hc : ((33109/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46823178217/1250000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((33109/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c51 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-996157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7634747/10000000) (δ := 5559/500000000) (ψ := 1151357/1000000) 220 137
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t51 : ((-1394969734167/10000000000000 : ℚ) : ℝ) ≤ stT220 51 := by
  have hc : ((-996207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1394969734167/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-996207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c52 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((251947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2606739/10000000) (δ := 11011/1000000000) (ψ := 1151357/1000000) 220 138
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t52 : ((698705667/10000000000 : ℚ) : ℝ) ≤ stT220 52 := by
  have hc : ((125961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((698705667/10000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((125961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c53 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((49767/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312357/5000000) (δ := 11099/1000000000) (ψ := 1151357/1000000) 220 139
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t53 : ((6835333201/100000000000 : ℚ) : ℝ) ≤ stT220 53 := by
  have hc : ((24881/50000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6835333201/100000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((24881/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c54 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-15576/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7655941/10000000) (δ := 11099/1000000000) (ψ := 1151357/1000000) 220 139
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t54 : ((-169578560599/1250000000000 : ℚ) : ℝ) ≤ stT220 54 := by
  have hc : ((-498457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169578560599/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-498457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c55 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((342573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1019991/5000000) (δ := 2799/250000000) (ψ := 1151357/1000000) 220 140
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t55 : ((115472845163/1250000000000 : ℚ) : ℝ) ≤ stT220 55 := by
  have hc : ((85637/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115472845163/1250000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((85637/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c56 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((33811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1878903/5000000) (δ := 11089/1000000000) (ψ := 1151357/1000000) 220 141
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t56 : ((11287108629/1250000000000 : ℚ) : ℝ) ≤ stT220 56 := by
  have hc : ((16893/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11287108629/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((16893/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c57 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-731141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2988487/5000000) (δ := 11089/1000000000) (ψ := 1151357/1000000) 220 141
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t57 : ((-968486608803/10000000000000 : ℚ) : ℝ) ≤ stT220 57 := by
  have hc : ((-731191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-968486608803/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-731191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c58 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((99781/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165499/10000000) (δ := 11021/1000000000) (ψ := 1151357/1000000) 220 142
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t58 : ((255883347/1953125000 : ℚ) : ℝ) ≤ stT220 58 := by
  have hc : ((3118/3125 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255883347/1953125000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((3118/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c59 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-170193/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3235771/5000000) (δ := 1391/125000000) (ψ := 1151357/1000000) 220 143
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t59 : ((-22158558367/200000000000 : ℚ) : ℝ) ≤ stT220 59 := by
  have hc : ((-170203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22158558367/200000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-170203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c60 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((222803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2772363/10000000) (δ := 1391/125000000) (ψ := 1151357/1000000) 220 143
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t60 : ((71901265333/1250000000000 : ℚ) : ℝ) ≤ stT220 60 := by
  have hc : ((111389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71901265333/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((111389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c61 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((8249/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1922243/5000000) (δ := 349/31250000) (ψ := 1151357/1000000) 220 144
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t61 : ((1318218879/312500000000 : ℚ) : ℝ) ≤ stT220 61 := by
  have hc : ((16473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1318218879/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((16473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c62 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-14117/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5098789/10000000) (δ := 349/31250000) (ψ := 1151357/1000000) 220 144
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t62 : ((-143444820897/2500000000000 : ℚ) : ℝ) ≤ stT220 62 := by
  have hc : ((-225897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143444820897/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-225897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c63 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((749439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904477/5000000) (δ := 553/50000000) (ψ := 1151357/1000000) 220 145
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t63 : ((944140962709/10000000000000 : ℚ) : ℝ) ≤ stT220 63 := by
  have hc : ((749389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((944140962709/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((749389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c64 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-920847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6852611/10000000) (δ := 553/50000000) (ψ := 1151357/1000000) 220 145
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t64 : ((-1151122170897/10000000000000 : ℚ) : ℝ) ≤ stT220 64 := by
  have hc : ((-920897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1151122170897/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-920897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c65 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((991403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164021/5000000) (δ := 221/20000000) (ψ := 1151357/1000000) 220 146
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t65 : ((1229621719491/10000000000000 : ℚ) : ℝ) ≤ stT220 65 := by
  have hc : ((991353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1229621719491/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((991353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c66 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-996301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47743/62500) (δ := 11157/1000000000) (ψ := 1151357/1000000) 220 147
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t66 : ((-245284678233/2000000000000 : ℚ) : ℝ) ≤ stT220 66 := by
  have hc : ((-996351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245284678233/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-996351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c67 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((968219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126393/2000000) (δ := 11157/1000000000) (ψ := 1151357/1000000) 220 147
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t67 : ((591403129143/5000000000000 : ℚ) : ℝ) ≤ stT220 67 := by
  have hc : ((968169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((591403129143/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((968169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c68 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-932141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3463847/5000000) (δ := 11139/1000000000) (ψ := 1151357/1000000) 220 148
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t68 : ((-1130448449689/10000000000000 : ℚ) : ℝ) ≤ stT220 68 := by
  have hc : ((-932191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1130448449689/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-932191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c69 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((904471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 550823/5000000) (δ := 11139/1000000000) (ψ := 1151357/1000000) 220 148
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t69 : ((544397228109/5000000000000 : ℚ) : ℝ) ≤ stT220 69 := by
  have hc : ((904421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544397228109/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((904421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c70 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-89401/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1673133/2500000) (δ := 1379/125000000) (ψ := 1151357/1000000) 220 149
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t70 : ((-53430321987/500000000000 : ℚ) : ℝ) ≤ stT220 70 := by
  have hc : ((-44703/50000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53430321987/500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-44703/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c71 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((903213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554499/5000000) (δ := 1379/125000000) (ψ := 1151357/1000000) 220 149
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t71 : ((1071856688303/10000000000000 : ℚ) : ℝ) ≤ stT220 71 := by
  have hc : ((903163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1071856688303/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((903163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c72 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-464519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13813/20000) (δ := 5539/500000000) (ψ := 1151357/1000000) 220 150
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t72 : ((-1069278669/9765625000 : ℚ) : ℝ) ≤ stT220 72 := by
  have hc : ((-14517/15625 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1069278669/9765625000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-14517/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c73 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((192651/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135963/2000000) (δ := 5539/500000000) (ψ := 1151357/1000000) 220 150
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t73 : ((225469145451/2000000000000 : ℚ) : ℝ) ≤ stT220 73 := by
  have hc : ((192641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225469145451/2000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((192641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c74 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-7939/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1886267/2500000) (δ := 5593/500000000) (ψ := 1151357/1000000) 220 151
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t74 : ((-46146849469/400000000000 : ℚ) : ℝ) ≤ stT220 74 := by
  have hc : ((-39697/40000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46146849469/400000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-39697/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c75 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((249473/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -162363/10000000) (δ := 5593/500000000) (ψ := 1151357/1000000) 220 151
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t75 : ((5761040787/50000000000 : ℚ) : ℝ) ≤ stT220 75 := by
  have hc : ((498921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5761040787/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((498921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c76 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-957499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7122497/10000000) (δ := 5593/500000000) (ψ := 1151357/1000000) 220 151
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t76 : ((-1098384349371/10000000000000 : ℚ) : ℝ) ≤ stT220 76 := by
  have hc : ((-957549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1098384349371/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-957549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c77 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((53009/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -348953/2500000) (δ := 1111/100000000) (ψ := 1151357/1000000) 220 152
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t77 : ((96649216287/1000000000000 : ℚ) : ℝ) ≤ stT220 77 := by
  have hc : ((424047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96649216287/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((424047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c78 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-651551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2850529/5000000) (δ := 1111/100000000) (ψ := 1151357/1000000) 220 152
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t78 : ((-368896738539/5000000000000 : ℚ) : ℝ) ≤ stT220 78 := by
  have hc : ((-651601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-368896738539/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-651601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c79 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((90547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -600091/2000000) (δ := 11003/1000000000) (ψ := 1151357/1000000) 220 153
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t79 : ((203718378003/5000000000000 : ℚ) : ℝ) ≤ stT220 79 := by
  have hc : ((181069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203718378003/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((181069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c80 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((1821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 783577/2000000) (δ := 11003/1000000000) (ψ := 1151357/1000000) 220 153
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t80 : ((501996817/1250000000000 : ℚ) : ℝ) ≤ stT220 80 := by
  have hc : ((449/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501996817/1250000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((449/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c81 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-6261/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4957703/10000000) (δ := 11107/1000000000) (ψ := 1151357/1000000) 220 154
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t81 : ((-27830161153/625000000000 : ℚ) : ℝ) ≤ stT220 81 := by
  have hc : ((-200377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27830161153/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-200377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c82 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((377107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 447713/2500000) (δ := 11107/1000000000) (ψ := 1151357/1000000) 220 154
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t82 : ((41641730883/500000000000 : ℚ) : ℝ) ≤ stT220 82 := by
  have hc : ((188541/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41641730883/500000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((188541/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c83 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-970991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3625171/5000000) (δ := 11189/1000000000) (ψ := 1151357/1000000) 220 155
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t83 : ((-1065856356363/10000000000000 : ℚ) : ℝ) ≤ stT220 83 := by
  have hc : ((-971041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1065856356363/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-971041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c84 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((15078/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -663459/10000000) (δ := 11007/500000000) (ψ := 1151357/1000000) 220 155
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t84 : ((526418800919/5000000000000 : ℚ) : ℝ) ≤ stT220 84 := by
  have hc : ((482471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((526418800919/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((482471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c85 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-347133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365343/625000) (δ := 11189/1000000000) (ψ := 1151357/1000000) 220 155
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t85 : ((-188272983087/2500000000000 : ℚ) : ℝ) ≤ stT220 85 := by
  have hc : ((-173579/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188272983087/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-173579/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c86 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((197617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137187/400000) (δ := 11081/1000000000) (ψ := 1151357/1000000) 220 156
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t86 : ((213041830409/10000000000000 : ℚ) : ℝ) ≤ stT220 86 := by
  have hc : ((197567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213041830409/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((197567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c87 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((48593/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146441/500000) (δ := 11081/1000000000) (ψ := 1151357/1000000) 220 156
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t87 : ((13022609429/312500000000 : ℚ) : ℝ) ≤ stT220 87 := by
  have hc : ((194347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13022609429/312500000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((194347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c88 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-213879/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3246679/5000000) (δ := 11029/1000000000) (ψ := 1151357/1000000) 220 157
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t88 : ((-114004597283/1250000000000 : ℚ) : ℝ) ≤ stT220 88 := by
  have hc : ((-427783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114004597283/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-427783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c89 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((248449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278633/10000000) (δ := 11029/1000000000) (ψ := 1151357/1000000) 220 157
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t89 : ((526683889381/5000000000000 : ℚ) : ℝ) ≤ stT220 89 := by
  have hc : ((496873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((526683889381/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((496873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c90 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-350171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2933341/5000000) (δ := 11029/1000000000) (ψ := 1151357/1000000) 220 157
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t90 : ((-92284788057/1250000000000 : ℚ) : ℝ) ≤ stT220 90 := by
  have hc : ((-87549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92284788057/1250000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-87549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c91 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((16301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -470483/1250000) (δ := 22067/1000000000) (ψ := 1151357/1000000) 220 158
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t91 : ((8537486967/1250000000000 : ℚ) : ℝ) ≤ stT220 91 := by
  have hc : ((32577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8537486967/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((32577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c92 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((311257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1123557/5000000) (δ := 87/7812500) (ψ := 1151357/1000000) 220 158
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t92 : ((1267506909/19531250000 : ℚ) : ℝ) ≤ stT220 92 := by
  have hc : ((9726/15625 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1267506909/19531250000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((9726/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c93 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-495407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502971/2000000) (δ := 279/25000000) (ψ := 1151357/1000000) 220 159
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t93 : ((-8027175051/78125000000 : ℚ) : ℝ) ≤ stT220 93 := by
  have hc : ((-61929/62500 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8027175051/78125000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-61929/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c94 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((794279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40811/250000) (δ := 279/25000000) (ψ := 1151357/1000000) 220 159
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t94 : ((819184469409/10000000000000 : ℚ) : ℝ) ≤ stT220 94 := by
  have hc : ((794229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((819184469409/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((794229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c95 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-104101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837543/2000000) (δ := 279/25000000) (ψ := 1151357/1000000) 220 159
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t95 : ((-106856738829/10000000000000 : ℚ) : ℝ) ≤ stT220 95 := by
  have hc : ((-104151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106856738829/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-104151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c96 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-16739/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5761033/10000000) (δ := 11053/1000000000) (ψ := 1151357/1000000) 220 160
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t96 : ((-68341802781/1000000000000 : ℚ) : ℝ) ≤ stT220 96 := by
  have hc : ((-66961/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68341802781/1000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-66961/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c97 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((499849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -61493/10000000) (δ := 11053/1000000000) (ψ := 1151357/1000000) 220 160
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t97 : ((15859196847/156250000000 : ℚ) : ℝ) ≤ stT220 97 := by
  have hc : ((31239/31250 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15859196847/156250000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((31239/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c98 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-122787/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2789791/5000000) (δ := 11053/1000000000) (ψ := 1151357/1000000) 220 160
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t98 : ((-124043757941/2000000000000 : ℚ) : ℝ) ≤ stT220 98 := by
  have hc : ((-122797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124043757941/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-122797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c99 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-244523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4544561/10000000) (δ := 11057/1000000000) (ψ := 1151357/1000000) 220 161
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t99 : ((-122902579387/5000000000000 : ℚ) : ℝ) ≤ stT220 99 := by
  have hc : ((-244573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122902579387/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-244573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c100 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((115459/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15361/156250) (δ := 11057/1000000000) (ψ := 1151357/1000000) 220 161
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t100 : ((461810538189/5000000000000 : ℚ) : ℝ) ≤ stT220 100 := by
  have hc : ((461811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461810538189/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((461811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c101 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-423823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403489/625000) (δ := 11057/1000000000) (ψ := 1151357/1000000) 220 161
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t101 : ((-26359054139/312500000000 : ℚ) : ℝ) ≤ stT220 101 := by
  have hc : ((-52981/62500 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26359054139/312500000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-52981/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c102 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((18719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1916687/5000000) (δ := 2233/200000000) (ψ := 1151357/1000000) 220 162
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t102 : ((9254904009/2500000000000 : ℚ) : ℝ) ≤ stT220 102 := by
  have hc : ((9347/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9254904009/2500000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((9347/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c103 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((81793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1532481/10000000) (δ := 2233/200000000) (ψ := 1151357/1000000) 220 162
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t103 : ((20147022063/250000000000 : ℚ) : ℝ) ≤ stT220 103 := by
  have hc : ((20447/25000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20147022063/250000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((20447/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c104 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-114987/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3423263/5000000) (δ := 2233/200000000) (ψ := 1151357/1000000) 220 162
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t104 : ((-451040784313/5000000000000 : ℚ) : ℝ) ≤ stT220 104 := by
  have hc : ((-459973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451040784313/5000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-459973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c105 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((32783/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3598213/10000000) (δ := 11131/1000000000) (ψ := 1151357/1000000) 220 163
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t105 : ((639614619/50000000000 : ℚ) : ℝ) ≤ stT220 105 := by
  have hc : ((65541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639614619/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((65541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c106 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((798481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50471/312500) (δ := 11131/1000000000) (ψ := 1151357/1000000) 220 163
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t106 : ((155100810767/2000000000000 : ℚ) : ℝ) ≤ stT220 106 := by
  have hc : ((798431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155100810767/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((798431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c107 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-454523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3389731/5000000) (δ := 11131/1000000000) (ψ := 1151357/1000000) 220 163
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t107 : ((-109857092469/1250000000000 : ℚ) : ℝ) ≤ stT220 107 := by
  have hc : ((-113637/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109857092469/1250000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-113637/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c108 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((11477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3812181/10000000) (δ := 689/62500000) (ψ := 1151357/1000000) 220 164
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t108 : ((88253721/20000000000 : ℚ) : ℝ) ≤ stT220 108 := by
  have hc : ((22929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88253721/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((22929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c109 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((876247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1256949/10000000) (δ := 689/62500000) (ψ := 1151357/1000000) 220 164
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t109 : ((419622133861/5000000000000 : ℚ) : ℝ) ≤ stT220 109 := by
  have hc : ((876197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((419622133861/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((876197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c110 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-404113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392489/625000) (δ := 689/62500000) (ψ := 1151357/1000000) 220 164
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t110 : ((-192665314947/2500000000000 : ℚ) : ℝ) ≤ stT220 110 := by
  have hc : ((-202069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192665314947/2500000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-202069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c111 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-207953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2225347/5000000) (δ := 5543/500000000) (ψ := 1151357/1000000) 220 165
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t111 : ((-98713855737/5000000000000 : ℚ) : ℝ) ≤ stT220 111 := by
  have hc : ((-208003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98713855737/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-208003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c112 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((981469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 120509/2500000) (δ := 5543/500000000) (ψ := 1151357/1000000) 220 165
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t112 : ((927353608709/10000000000000 : ℚ) : ℝ) ≤ stT220 112 := by
  have hc : ((981419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((927353608709/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((981419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c113 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-546013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2685493/5000000) (δ := 5543/500000000) (ψ := 1151357/1000000) 220 165
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t113 : ((-513692931423/10000000000000 : ℚ) : ℝ) ≤ stT220 113 := by
  have hc : ((-546063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-513692931423/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-546063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c114 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-292817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5491147/10000000) (δ := 11193/1000000000) (ψ := 1151357/1000000) 220 166
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t114 : ((-68567929353/1250000000000 : ℚ) : ℝ) ≤ stT220 114 := by
  have hc : ((-146421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68567929353/1250000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-146421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c115 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((962413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171903/2500000) (δ := 11193/1000000000) (ψ := 1151357/1000000) 220 166
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t115 : ((112175918369/1250000000000 : ℚ) : ℝ) ≤ stT220 115 := by
  have hc : ((962363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112175918369/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((962363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c116 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-11777/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 254643/625000) (δ := 11193/1000000000) (ψ := 1151357/1000000) 220 166
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t116 : ((-10943958399/2000000000000 : ℚ) : ℝ) ≤ stT220 116 := by
  have hc : ((-11787/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10943958399/2000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-11787/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c117 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-58121/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3456293/5000000) (δ := 11103/1000000000) (ψ := 1151357/1000000) 220 167
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t117 : ((-429886493493/5000000000000 : ℚ) : ℝ) ≤ stT220 117 := by
  have hc : ((-464993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-429886493493/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-464993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c118 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((627327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2231701/10000000) (δ := 11103/1000000000) (ψ := 1151357/1000000) 220 167
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t118 : ((288727448499/5000000000000 : ℚ) : ℝ) ≤ stT220 118 := by
  have hc : ((627277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288727448499/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((627277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c119 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((570357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2409639/10000000) (δ := 11103/1000000000) (ψ := 1151357/1000000) 220 167
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t119 : ((261399643143/5000000000000 : ℚ) : ℝ) ≤ stT220 119 := by
  have hc : ((570307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261399643143/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((570307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c120 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-471923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1753051/2500000) (δ := 11103/1000000000) (ψ := 1151357/1000000) 220 167
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t120 : ((-107706910677/1250000000000 : ℚ) : ℝ) ≤ stT220 120 := by
  have hc : ((-117987/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107706910677/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-117987/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c121 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-1021/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4131419/10000000) (δ := 43/3906250) (ψ := 1151357/1000000) 220 168
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t121 : ((-7430000743/1000000000000 : ℚ) : ℝ) ≤ stT220 121 := by
  have hc : ((-8173/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7430000743/1000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-8173/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c122 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((493761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98839/2500000) (δ := 43/3906250) (ψ := 1151357/1000000) 220 168
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t122 : ((55875917969/625000000000 : ℚ) : ℝ) ≤ stT220 122 := by
  have hc : ((61717/62500 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55875917969/625000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((61717/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c123 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-373957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4885171/10000000) (δ := 43/3906250) (ψ := 1151357/1000000) 220 168
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t123 : ((-33723089169/1000000000000 : ℚ) : ℝ) ≤ stT220 123 := by
  have hc : ((-374007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33723089169/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-374007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c124 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-828787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592333/2500000) (δ := 2223/200000000) (ψ := 1151357/1000000) 220 169
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t124 : ((-744318004599/10000000000000 : ℚ) : ℝ) ≤ stT220 124 := by
  have hc : ((-828837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-744318004599/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-828837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c125 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((710457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -975811/5000000) (δ := 2223/200000000) (ψ := 1151357/1000000) 220 169
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t125 : ((635407201789/10000000000000 : ℚ) : ℝ) ≤ stT220 125 := by
  have hc : ((710407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635407201789/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((710407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c126 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((112671/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 303861/1250000) (δ := 2223/200000000) (ψ := 1151357/1000000) 220 169
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t126 : ((10036630507/200000000000 : ℚ) : ℝ) ≤ stT220 126 := by
  have hc : ((112661/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10036630507/200000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((112661/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c127 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-454459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6778693/10000000) (δ := 2223/200000000) (ψ := 1151357/1000000) 220 169
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t127 : ((-100822389697/1250000000000 : ℚ) : ℝ) ≤ stT220 127 := by
  have hc : ((-113621/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100822389697/1250000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-113621/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c128 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-13597/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4615511/10000000) (δ := 11181/1000000000) (ψ := 1151357/1000000) 220 170
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t128 : ((-6010190229/250000000000 : ℚ) : ℝ) ≤ stT220 128 := by
  have hc : ((-27199/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6010190229/250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-27199/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c129 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((991019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335301/10000000) (δ := 11181/1000000000) (ψ := 1151357/1000000) 220 170
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t129 : ((17449973121/200000000000 : ℚ) : ℝ) ≤ stT220 129 := by
  have hc : ((990969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17449973121/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((990969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c130 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((6077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3911799/10000000) (δ := 11181/1000000000) (ψ := 1151357/1000000) 220 170
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t130 : ((2643014283/5000000000000 : ℚ) : ℝ) ≤ stT220 130 := by
  have hc : ((6027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2643014283/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((6027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c131 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-994069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7581569/10000000) (δ := 5537/500000000) (ψ := 1151357/1000000) 220 171
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t131 : ((-173713348179/2000000000000 : ℚ) : ℝ) ≤ stT220 131 := by
  have hc : ((-994119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173713348179/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-994119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c132 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((41923/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3399039/10000000) (δ := 5537/500000000) (ψ := 1151357/1000000) 220 171
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t132 : ((9120143061/500000000000 : ℚ) : ℝ) ≤ stT220 132 := by
  have hc : ((41913/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9120143061/500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((41913/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c133 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((955109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 751921/10000000) (δ := 5537/500000000) (ψ := 1151357/1000000) 220 171
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t133 : ((828140254431/10000000000000 : ℚ) : ℝ) ≤ stT220 133 := by
  have hc : ((955059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((828140254431/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((955059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c134 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-46123/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4871779/10000000) (δ := 22129/1000000000) (ψ := 1151357/1000000) 220 171
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t134 : ((-159398516273/5000000000000 : ℚ) : ℝ) ≤ stT220 134 := by
  have hc : ((-184517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159398516273/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-184517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c135 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-14118/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3373481/5000000) (δ := 2759/250000000) (ψ := 1151357/1000000) 220 172
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t135 : ((-388848404063/5000000000000 : ℚ) : ℝ) ≤ stT220 135 := by
  have hc : ((-451801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-388848404063/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-451801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c136 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((475589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2687907/10000000) (δ := 2759/250000000) (ψ := 1151357/1000000) 220 172
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t136 : ((101942722047/2500000000000 : ℚ) : ℝ) ≤ stT220 136 := by
  have hc : ((475539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101942722047/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((475539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c137 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((429731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167681/1250000) (δ := 2759/250000000) (ψ := 1151357/1000000) 220 172
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t137 : ((183561164521/2500000000000 : ℚ) : ℝ) ≤ stT220 137 := by
  have hc : ((214853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183561164521/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((214853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c138 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-67009/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5341433/10000000) (δ := 2759/250000000) (ψ := 1151357/1000000) 220 172
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t138 : ((-228188802677/5000000000000 : ℚ) : ℝ) ≤ stT220 138 := by
  have hc : ((-268061/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228188802677/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-268061/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c139 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-834569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1279073/2000000) (δ := 1393/125000000) (ψ := 1151357/1000000) 220 173
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t139 : ((-707914654991/10000000000000 : ℚ) : ℝ) ≤ stT220 139 := by
  have hc : ((-834619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-707914654991/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-834619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c140 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((556129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245269/1000000) (δ := 1393/125000000) (ψ := 1151357/1000000) 220 173
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t140 : ((234986195583/5000000000000 : ℚ) : ℝ) ≤ stT220 140 := by
  have hc : ((556079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234986195583/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((556079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c141 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((833849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36547/250000) (δ := 1393/125000000) (ψ := 1151357/1000000) 220 173
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t141 : ((702184661649/10000000000000 : ℚ) : ℝ) ≤ stT220 141 := by
  have hc : ((833799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((702184661649/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((833799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c142 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-538571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133721/250000) (δ := 1393/125000000) (ψ := 1151357/1000000) 220 173
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t142 : ((-226000524011/5000000000000 : ℚ) : ℝ) ≤ stT220 142 := by
  have hc : ((-538621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226000524011/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-538621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c143 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-428387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1624861/2500000) (δ := 697/62500000) (ψ := 1151357/1000000) 220 174
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t143 : ((-89564134029/1250000000000 : ℚ) : ℝ) ≤ stT220 143 := by
  have hc : ((-107103/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89564134029/1250000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-107103/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c144 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((483029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1333357/5000000) (δ := 697/62500000) (ψ := 1151357/1000000) 220 174
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t144 : ((402482339007/10000000000000 : ℚ) : ℝ) ≤ stT220 144 := by
  have hc : ((482979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402482339007/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((482979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c145 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((448949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1139561/10000000) (δ := 697/62500000) (ψ := 1151357/1000000) 220 174
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t145 : ((46601341437/625000000000 : ℚ) : ℝ) ≤ stT220 145 := by
  have hc : ((112231/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46601341437/625000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((112231/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c146 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-193357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 614957/1250000) (δ := 697/62500000) (ψ := 1151357/1000000) 220 174
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t146 : ((-40011025873/1250000000000 : ℚ) : ℝ) ≤ stT220 146 := by
  have hc : ((-96691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40011025873/1250000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-96691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c147 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-946699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3517031/5000000) (δ := 2209/200000000) (ψ := 1151357/1000000) 220 175
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t147 : ((-780866267463/10000000000000 : ℚ) : ℝ) ≤ stT220 147 := by
  have hc : ((-946749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-780866267463/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-946749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c148 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((4923/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305227/10000000) (δ := 2209/200000000) (ψ := 1151357/1000000) 220 175
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t148 : ((1011463617/50000000000 : ℚ) : ℝ) ≤ stT220 148 := by
  have hc : ((2461/10000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1011463617/50000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((2461/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c149 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((987321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6227/156250) (δ := 2209/200000000) (ψ := 1151357/1000000) 220 175
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t149 : ((808803008601/10000000000000 : ℚ) : ℝ) ≤ stT220 149 := by
  have hc : ((987271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((808803008601/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((987271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c150 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-60137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4077423/10000000) (δ := 2209/200000000) (ψ := 1151357/1000000) 220 175
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t150 : ((-49142504939/10000000000000 : ℚ) : ℝ) ≤ stT220 150 := by
  have hc : ((-60187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49142504939/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-60187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c151 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-998809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7731953/10000000) (δ := 2209/200000000) (ψ := 1151357/1000000) 220 175
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t151 : ((-812860466751/10000000000000 : ℚ) : ℝ) ≤ stT220 151 := by
  have hc : ((-998859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812860466751/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-998859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c152 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-10417/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6953/16000) (δ := 2213/200000000) (ψ := 1151357/1000000) 220 176
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t152 : ((-16903693497/1250000000000 : ℚ) : ℝ) ≤ stT220 152 := by
  have hc : ((-83361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16903693497/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-83361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c153 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((956621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -147811/2000000) (δ := 2213/200000000) (ψ := 1151357/1000000) 220 176
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t153 : ((193335434523/2500000000000 : ℚ) : ℝ) ≤ stT220 153 := by
  have hc : ((956571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193335434523/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((956571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c154 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((419763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 284403/1000000) (δ := 2213/200000000) (ψ := 1151357/1000000) 220 176
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t154 : ((169106984543/5000000000000 : ℚ) : ℝ) ≤ stT220 154 := by
  have hc : ((419713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169106984543/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((419713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c155 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-418223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1280781/2000000) (δ := 2213/200000000) (ψ := 1151357/1000000) 220 176
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t155 : ((-2099657241/31250000000 : ℚ) : ℝ) ≤ stT220 155 := by
  have hc : ((-52281/62500 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2099657241/31250000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-52281/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c156 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-13427/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5767063/10000000) (δ := 2793/250000000) (ψ := 1151357/1000000) 220 177
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t156 : ((-2687751837/50000000000 : ℚ) : ℝ) ≤ stT220 156 := by
  have hc : ((-3357/5000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2687751837/50000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-3357/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c157 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((155193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2252673/10000000) (δ := 2793/250000000) (ψ := 1151357/1000000) 220 177
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t157 : ((123847384523/2500000000000 : ℚ) : ℝ) ≤ stT220 157 := by
  have hc : ((310361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123847384523/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((310361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c158 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((87961/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239387/10000000) (δ := 2793/250000000) (ψ := 1151357/1000000) 220 177
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t158 : ((17493502873/250000000000 : ℚ) : ℝ) ≤ stT220 158 := by
  have hc : ((21989/25000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17493502873/250000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((21989/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c159 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-153949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4709447/10000000) (δ := 2793/250000000) (ψ := 1151357/1000000) 220 177
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t159 : ((-15263673581/625000000000 : ℚ) : ℝ) ≤ stT220 159 := by
  have hc : ((-76987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15263673581/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-76987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c160 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-248157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7550237/10000000) (δ := 2781/250000000) (ψ := 1151357/1000000) 220 178
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t160 : ((-39239072323/500000000000 : ℚ) : ℝ) ≤ stT220 160 := by
  have hc : ((-496339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39239072323/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-496339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c161 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-19627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2061731/5000000) (δ := 2781/250000000) (ψ := 1151357/1000000) 220 178
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t161 : ((-30956211969/5000000000000 : ℚ) : ℝ) ≤ stT220 161 := by
  have hc : ((-39279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30956211969/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-39279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c162 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((59941/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -358931/5000000) (δ := 2781/250000000) (ψ := 1151357/1000000) 220 178
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t162 : ((188366520011/2500000000000 : ℚ) : ℝ) ≤ stT220 162 := by
  have hc : ((479503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188366520011/2500000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((479503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c163 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((96601/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2666783/10000000) (δ := 2781/250000000) (ψ := 1151357/1000000) 220 178
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t163 : ((3782793333/100000000000 : ℚ) : ℝ) ≤ stT220 163 := by
  have hc : ((96591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3782793333/100000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((96591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c164 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-745631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6030693/10000000) (δ := 2781/250000000) (ψ := 1151357/1000000) 220 178
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t164 : ((-582279176789/10000000000000 : ℚ) : ℝ) ≤ stT220 164 := by
  have hc : ((-745681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-582279176789/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-745681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c165 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-164151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316691/500000) (δ := 1377/125000000) (ψ := 1151357/1000000) 220 179
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t165 : ((-127799174339/2000000000000 : ℚ) : ℝ) ≤ stT220 165 := by
  have hc : ((-164161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127799174339/2000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-164161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c166 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((358419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602111/2000000) (δ := 1377/125000000) (ψ := 1151357/1000000) 220 179
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t166 : ((5562961987/200000000000 : ℚ) : ℝ) ≤ stT220 166 := by
  have hc : ((358369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5562961987/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((358369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c167 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((993149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183/6250) (δ := 1377/125000000) (ψ := 1151357/1000000) 220 179
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t167 : ((768482847477/10000000000000 : ℚ) : ℝ) ≤ stT220 167 := by
  have hc : ((993099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((768482847477/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((993099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c168 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((27959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715271/2000000) (δ := 1377/125000000) (ψ := 1151357/1000000) 220 179
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t168 : ((5390775171/500000000000 : ℚ) : ℝ) ≤ stT220 168 := by
  have hc : ((27949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5390775171/500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((27949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c169 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-918947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1368099/2000000) (δ := 1377/125000000) (ψ := 1151357/1000000) 220 179
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t169 : ((-706920981307/10000000000000 : ℚ) : ℝ) ≤ stT220 169 := by
  have hc : ((-918997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-706920981307/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-918997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c170 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-627437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5622633/10000000) (δ := 5547/500000000) (ψ := 1151357/1000000) 220 180
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t170 : ((-96252113391/2000000000000 : ℚ) : ℝ) ≤ stT220 170 := by
  have hc : ((-627487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96252113391/2000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-627487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c171 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((574559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599207/2500000) (δ := 5547/500000000) (ψ := 1151357/1000000) 220 180
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t171 : ((439337947971/10000000000000 : ℚ) : ℝ) ≤ stT220 171 := by
  have hc : ((574509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439337947971/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((574509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c172 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((236987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 810167/10000000) (δ := 5547/500000000) (ψ := 1151357/1000000) 220 180
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t172 : ((90345580227/1250000000000 : ℚ) : ℝ) ≤ stT220 172 := by
  have hc : ((473949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90345580227/1250000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((473949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c173 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-28629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 999643/2500000) (δ := 5547/500000000) (ψ := 1151357/1000000) 220 180
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t173 : ((-10902121097/5000000000000 : ℚ) : ℝ) ≤ stT220 173 := by
  have hc : ((-28679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10902121097/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-28679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c174 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-30083/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7168607/10000000) (δ := 5547/500000000) (ψ := 1151357/1000000) 220 180
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t174 : ((-364913227947/5000000000000 : ℚ) : ℝ) ≤ stT220 174 := by
  have hc : ((-481353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364913227947/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-481353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c175 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-275763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5387471/10000000) (δ := 11201/1000000000) (ψ := 1151357/1000000) 220 181
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t175 : ((-52119036763/1250000000000 : ℚ) : ℝ) ≤ stT220 175 := by
  have hc : ((-68947/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52119036763/1250000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-68947/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c176 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((62049/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2253571/10000000) (δ := 11201/1000000000) (ψ := 1151357/1000000) 220 181
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t176 : ((5845925279/125000000000 : ℚ) : ℝ) ≤ stT220 176 := by
  have hc : ((15511/25000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5845925279/125000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((15511/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c177 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((941059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 862619/10000000) (δ := 11201/1000000000) (ψ := 1151357/1000000) 220 181
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t177 : ((353652825407/5000000000000 : ℚ) : ℝ) ≤ stT220 177 := by
  have hc : ((941009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((353652825407/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((941009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c178 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-13687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3961209/10000000) (δ := 11201/1000000000) (ψ := 1151357/1000000) 220 181
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t178 : ((-2574080271/2500000000000 : ℚ) : ℝ) ≤ stT220 178 := by
  have hc : ((-13737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2574080271/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-13737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c179 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-947777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3521237/5000000) (δ := 11201/1000000000) (ψ := 1151357/1000000) 220 181
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t179 : ((-177110005393/2500000000000 : ℚ) : ℝ) ≤ stT220 179 := by
  have hc : ((-947827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177110005393/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-947827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c180 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-620813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35009/62500) (δ := 2219/200000000) (ψ := 1151357/1000000) 220 182
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t180 : ((-115690990557/2500000000000 : ℚ) : ℝ) ≤ stT220 180 := by
  have hc : ((-620863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115690990557/2500000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-620863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c181 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((521889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -255433/1000000) (δ := 2219/200000000) (ψ := 1151357/1000000) 220 182
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t181 : ((193939898833/5000000000000 : ℚ) : ℝ) ≤ stT220 181 := by
  have hc : ((521839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193939898833/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((521839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c182 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((245483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9519/200000) (δ := 2219/200000000) (ψ := 1151357/1000000) 220 182
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t182 : ((363909525309/5000000000000 : ℚ) : ℝ) ≤ stT220 182 := by
  have hc : ((490941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((363909525309/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((490941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c183 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((43509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139587/400000) (δ := 2219/200000000) (ψ := 1151357/1000000) 220 182
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t183 : ((64307052453/5000000000000 : ℚ) : ℝ) ≤ stT220 183 := by
  have hc : ((86993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64307052453/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((86993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c184 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-854187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1297391/2000000) (δ := 2219/200000000) (ψ := 1151357/1000000) 220 182
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t184 : ((-62975205877/1000000000000 : ℚ) : ℝ) ≤ stT220 184 := by
  have hc : ((-854237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62975205877/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-854237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c185 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-199683/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6239953/10000000) (δ := 2203/200000000) (ψ := 1151357/1000000) 220 183
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t185 : ((-58727650813/1000000000000 : ℚ) : ℝ) ≤ stT220 185 := by
  have hc : ((-399391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58727650813/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-399391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c186 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((51569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3275013/10000000) (δ := 2203/200000000) (ψ := 1151357/1000000) 220 183
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t186 : ((7560972673/400000000000 : ℚ) : ℝ) ≤ stT220 186 := by
  have hc : ((51559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7560972673/400000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((51559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c187 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((495757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325913/10000000) (δ := 2203/200000000) (ψ := 1151357/1000000) 220 183
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t187 : ((11328591597/156250000000 : ℚ) : ℝ) ≤ stT220 187 := by
  have hc : ((123933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11328591597/156250000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((123933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c188 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((100733/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1303701/5000000) (δ := 2203/200000000) (ψ := 1151357/1000000) 220 183
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t188 : ((18364925313/500000000000 : ℚ) : ℝ) ≤ stT220 188 := by
  have hc : ((100723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18364925313/500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((100723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c189 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-596623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5525207/10000000) (δ := 2203/200000000) (ψ := 1151357/1000000) 220 183
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t189 : ((-434015763489/10000000000000 : ℚ) : ℝ) ≤ stT220 189 := by
  have hc : ((-596673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434015763489/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-596673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c190 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-243449/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3640203/5000000) (δ := 11123/1000000000) (ψ := 1151357/1000000) 220 184
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t190 : ((-353251437271/5000000000000 : ℚ) : ℝ) ≤ stT220 190 := by
  have hc : ((-486923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353251437271/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-486923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c191 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-185419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1098309/2500000) (δ := 11123/1000000000) (ψ := 1151357/1000000) 220 184
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t191 : ((-5368029267/400000000000 : ℚ) : ℝ) ≤ stT220 191 := by
  have hc : ((-185469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5368029267/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-185469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c192 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((20513/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1521191/10000000) (δ := 11123/1000000000) (ψ := 1151357/1000000) 220 184
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t192 : ((59212253289/1000000000000 : ℚ) : ℝ) ≤ stT220 192 := by
  have hc : ((82047/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59212253289/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((82047/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c193 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((172117/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1335949/10000000) (δ := 11123/1000000000) (ψ := 1151357/1000000) 220 184
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t193 : ((24777040041/400000000000 : ℚ) : ℝ) ≤ stT220 193 := by
  have hc : ((172107/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24777040041/400000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((172107/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c194 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-50187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4178349/10000000) (δ := 11123/1000000000) (ψ := 1151357/1000000) 220 184
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t194 : ((-9012539327/1250000000000 : ℚ) : ℝ) ≤ stT220 194 := by
  have hc : ((-12553/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9012539327/1250000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-12553/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c195 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-943039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7006119/10000000) (δ := 11123/1000000000) (ψ := 1151357/1000000) 220 184
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t195 : ((-135072035847/2000000000000 : ℚ) : ℝ) ≤ stT220 195 := by
  have hc : ((-943089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135072035847/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-943089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c196 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-176639/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294427/500000) (δ := 11173/1000000000) (ψ := 1151357/1000000) 220 185
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t196 : ((-126179693329/2500000000000 : ℚ) : ℝ) ≤ stT220 196 := by
  have hc : ((-353303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126179693329/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-353303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c197 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((20547/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -617907/2000000) (δ := 11173/1000000000) (ψ := 1151357/1000000) 220 185
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t197 : ((11709515697/500000000000 : ℚ) : ℝ) ≤ stT220 197 := by
  have hc : ((164351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11709515697/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((164351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c198 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((992581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3809/125000) (δ := 11173/1000000000) (ψ := 1151357/1000000) 220 185
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t198 : ((705361013239/10000000000000 : ℚ) : ℝ) ≤ stT220 198 := by
  have hc : ((992531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((705361013239/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((992531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c199 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((551673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246607/1000000) (δ := 11173/1000000000) (ψ := 1151357/1000000) 220 185
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t199 : ((391035063863/10000000000000 : ℚ) : ℝ) ≤ stT220 199 := by
  have hc : ((551623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391035063863/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((551623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c200 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-19819/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1044589/2000000) (δ := 11173/1000000000) (ψ := 1151357/1000000) 220 185
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t200 : ((-14015567847/400000000000 : ℚ) : ℝ) ≤ stT220 200 := by
  have hc : ((-19821/40000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14015567847/400000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-19821/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c201 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-499497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3870919/5000000) (δ := 5533/500000000) (ψ := 1151357/1000000) 220 186
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t201 : ((-88083961153/1250000000000 : ℚ) : ℝ) ≤ stT220 201 := by
  have hc : ((-249761/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88083961153/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-249761/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c202 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-84127/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5012353/10000000) (δ := 5533/500000000) (ψ := 1151357/1000000) 220 186
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t202 : ((-29599312463/1000000000000 : ℚ) : ℝ) ≤ stT220 202 := by
  have hc : ((-84137/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29599312463/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-84137/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c203 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((607001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71759/312500) (δ := 5533/500000000) (ψ := 1151357/1000000) 220 186
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t203 : ((212997921381/5000000000000 : ℚ) : ℝ) ≤ stT220 203 := by
  have hc : ((606951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212997921381/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((606951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c204 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((197363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101603/2500000) (δ := 5533/500000000) (ψ := 1151357/1000000) 220 186
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t204 : ((6908736471/100000000000 : ℚ) : ℝ) ≤ stT220 204 := by
  have hc : ((197353/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6908736471/100000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((197353/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c205 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((163171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 386989/1250000) (δ := 5533/500000000) (ψ := 1151357/1000000) 220 186
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t205 : ((5697303039/250000000000 : ℚ) : ℝ) ≤ stT220 205 := by
  have hc : ((81573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5697303039/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((81573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c206 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-168227/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2886161/5000000) (δ := 5533/500000000) (ψ := 1151357/1000000) 220 186
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t206 : ((-117218179793/2500000000000 : ℚ) : ℝ) ≤ stT220 206 := by
  have hc : ((-336479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117218179793/2500000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-336479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c207 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-194609/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7272211/10000000) (δ := 2761/250000000) (ψ := 1151357/1000000) 220 187
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t207 : ((-135269741331/2000000000000 : ℚ) : ℝ) ≤ stT220 207 := by
  have hc : ((-194619/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135269741331/2000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-194619/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c208 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-274281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1155399/2500000) (δ := 2761/250000000) (ψ := 1151357/1000000) 220 187
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t208 : ((-1486051027/78125000000 : ℚ) : ℝ) ≤ stT220 208 := by
  have hc : ((-274331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1486051027/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-274331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c209 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((701373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -991843/5000000) (δ := 2761/250000000) (ψ := 1151357/1000000) 220 187
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t209 : ((242557468811/5000000000000 : ℚ) : ℝ) ≤ stT220 209 := by
  have hc : ((701323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242557468811/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((701323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c210 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((193449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 641629/10000000) (δ := 2761/250000000) (ψ := 1151357/1000000) 220 187
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t210 : ((26697096707/400000000000 : ℚ) : ℝ) ≤ stT220 210 := by
  have hc : ((193439/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26697096707/400000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((193439/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c211 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((13289/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3254459/10000000) (δ := 2761/250000000) (ψ := 1151357/1000000) 220 187
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t211 : ((4573399311/250000000000 : ℚ) : ℝ) ≤ stT220 211 := by
  have hc : ((26573/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4573399311/250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((26573/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c212 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-348487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2927457/5000000) (δ := 2761/250000000) (ψ := 1151357/1000000) 220 187
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t212 : ((-7479971473/156250000000 : ℚ) : ℝ) ≤ stT220 212 := by
  have hc : ((-10891/15625 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7479971473/156250000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-10891/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c213 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-486179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1816201/2500000) (δ := 11151/1000000000) (ψ := 1151357/1000000) 220 188
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t213 : ((-83285408139/1250000000000 : ℚ) : ℝ) ≤ stT220 213 := by
  have hc : ((-121551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83285408139/1250000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-121551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c214 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-37497/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4688659/10000000) (δ := 11151/1000000000) (ψ := 1151357/1000000) 220 188
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t214 : ((-51273393309/2500000000000 : ℚ) : ℝ) ≤ stT220 214 := by
  have hc : ((-150013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51273393309/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-150013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c215 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((165029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2124559/10000000) (δ := 11151/1000000000) (ψ := 1151357/1000000) 220 188
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t215 : ((112540262901/2500000000000 : ℚ) : ℝ) ≤ stT220 215 := by
  have hc : ((330033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112540262901/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((330033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c216 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((246351/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 427661/10000000) (δ := 11151/1000000000) (ψ := 1151357/1000000) 220 188
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t216 : ((335223835601/5000000000000 : ℚ) : ℝ) ≤ stT220 216 := by
  have hc : ((492677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335223835601/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((492677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c217 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((374237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 371007/1250000) (δ := 11151/1000000000) (ψ := 1151357/1000000) 220 188
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t217 : ((63503649957/2500000000000 : ℚ) : ℝ) ≤ stT220 217 := by
  have hc : ((374187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63503649957/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((374187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c218 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-587463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5496791/10000000) (δ := 11151/1000000000) (ψ := 1151357/1000000) 220 188
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t218 : ((-198957164859/5000000000000 : ℚ) : ℝ) ≤ stT220 218 := by
  have hc : ((-587513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198957164859/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-587513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c219 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-997953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923497/2500000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t219 : ((-337194275607/5000000000000 : ℚ) : ℝ) ≤ stT220 219 := by
  have hc : ((-998003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337194275607/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-998003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c220 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-48339/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2594149/5000000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t220 : ((-20370953/625000000 : ℚ) : ℝ) ≤ stT220 220 := by
  have hc : ((-6043/12500 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20370953/625000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-6043/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c221 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((236733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1346969/5000000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t221 : ((1243959717/39062500000 : ℚ) : ℝ) ≤ stT220 221 := by
  have hc : ((59177/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1243959717/39062500000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((59177/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c222 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((249111/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -52727/2500000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t222 : ((83591976433/1250000000000 : ℚ) : ℝ) ≤ stT220 222 := by
  have hc : ((498197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83591976433/1250000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((498197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c223 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((309077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565253/2500000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t223 : ((51739090687/1250000000000 : ℚ) : ℝ) ≤ stT220 223 := by
  have hc : ((77263/125000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51739090687/1250000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((77263/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c224 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-19539/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4721877/10000000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t224 : ((-52228595949/2500000000000 : ℚ) : ℝ) ≤ stT220 224 := by
  have hc : ((-156337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52228595949/2500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-156337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c225 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-963/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7171797/10000000) (δ := 2229/200000000) (ψ := 1151357/1000000) 220 189
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t225 : ((-12840673087/200000000000 : ℚ) : ℝ) ≤ stT220 225 := by
  have hc : ((-19261/20000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12840673087/200000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-19261/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c226 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-381541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6097163/10000000) (δ := 11083/500000000) (ψ := 1151357/1000000) 220 190
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t226 : ((-126907134553/2500000000000 : ℚ) : ℝ) ≤ stT220 226 := by
  have hc : ((-190783/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126907134553/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-190783/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c227 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((103059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834443/5000000) (δ := 11037/1000000000) (ψ := 1151357/1000000) 220 190
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t227 : ((68369442507/10000000000000 : ℚ) : ℝ) ≤ stT220 227 := by
  have hc : ((103009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68369442507/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((103009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c228 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((219333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -625653/5000000) (δ := 11037/1000000000) (ψ := 1151357/1000000) 220 190
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t228 : ((145248510253/2500000000000 : ℚ) : ℝ) ≤ stT220 228 := by
  have hc : ((438641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145248510253/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((438641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c229 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((179007/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 577857/5000000) (δ := 11037/1000000000) (ψ := 1151357/1000000) 220 190
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t229 : ((59142219773/1000000000000 : ℚ) : ℝ) ≤ stT220 229 := by
  have hc : ((178997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59142219773/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((178997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c230 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((4667/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3552229/10000000) (δ := 11037/1000000000) (ψ := 1151357/1000000) 220 190
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t230 : ((2461036943/250000000000 : ℚ) : ℝ) ≤ stT220 230 := by
  have hc : ((74647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2461036943/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((74647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c231 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-360257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5938349/10000000) (δ := 11037/1000000000) (ψ := 1151357/1000000) 220 190
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t231 : ((-3703879101/78125000000 : ℚ) : ℝ) ≤ stT220 231 := by
  have hc : ((-180141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3703879101/78125000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-180141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c232 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-983109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3696917/5000000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t232 : ((-645476327747/10000000000000 : ℚ) : ℝ) ≤ stT220 232 := by
  have hc : ((-983159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-645476327747/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-983159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c233 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-106597/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5028229/10000000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t233 : ((-69842228859/2500000000000 : ℚ) : ℝ) ≤ stT220 233 := by
  have hc : ((-213219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69842228859/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-213219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c234 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((120229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -334093/1250000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t234 : ((3929396519/125000000000 : ℚ) : ℝ) ≤ stT220 234 := by
  have hc : ((240433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3929396519/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((240433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c235 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((991441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81831/2500000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t235 : ((80839013531/1250000000000 : ℚ) : ℝ) ≤ stT220 235 := by
  have hc : ((991391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80839013531/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((991391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c236 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((694367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2008141/10000000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t236 : ((7061898207/156250000000 : ℚ) : ℝ) ≤ stT220 236 := by
  have hc : ((694317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7061898207/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((694317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c237 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-161969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2166853/5000000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t237 : ((-10524268183/1000000000000 : ℚ) : ℝ) ≤ stT220 237 := by
  have hc : ((-162019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10524268183/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-162019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c238 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-443081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6649481/10000000) (δ := 11073/1000000000) (ψ := 1151357/1000000) 220 191
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t238 : ((-35902885203/625000000000 : ℚ) : ℝ) ≤ stT220 238 := by
  have hc : ((-221553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35902885203/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-221553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c239 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-5653/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6752387/10000000) (δ := 559/50000000) (ψ := 1151357/1000000) 220 192
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t239 : ((-58509251691/1000000000000 : ℚ) : ℝ) ≤ stT220 239 := by
  have hc : ((-90453/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58509251691/1000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-90453/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c240 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-52499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4455917/10000000) (δ := 559/50000000) (ψ := 1151357/1000000) 220 192
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t240 : ((-33896068227/2500000000000 : ℚ) : ℝ) ≤ stT220 240 := by
  have hc : ((-105023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33896068227/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-105023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c241 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((323327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2169017/10000000) (δ := 559/50000000) (ψ := 1151357/1000000) 220 192
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t241 : ((26032115389/625000000000 : ℚ) : ℝ) ≤ stT220 241 := by
  have hc : ((161651/250000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26032115389/625000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((161651/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c242 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((49953/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108423/10000000) (δ := 559/50000000) (ψ := 1151357/1000000) 220 192
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t242 : ((8027345053/125000000000 : ℚ) : ℝ) ≤ stT220 242 := by
  have hc : ((99901/100000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8027345053/125000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((99901/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c243 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((581209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1188229/5000000) (δ := 559/50000000) (ψ := 1151357/1000000) 220 192
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t243 : ((745626997/20000000000 : ℚ) : ℝ) ≤ stT220 243 := by
  have hc : ((581159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((745626997/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((581159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c244 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-279509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2317599/5000000) (δ := 559/50000000) (ψ := 1151357/1000000) 220 192
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t244 : ((-35793895683/2000000000000 : ℚ) : ℝ) ≤ stT220 244 := by
  have hc : ((-279559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35793895683/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-279559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c245 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-231443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 688467/1000000) (δ := 22023/1000000000) (ψ := 1151357/1000000) 220 192
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t245 : ((-295743190947/5000000000000 : ℚ) : ℝ) ≤ stT220 245 := by
  have hc : ((-462911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295743190947/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-462911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c246 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-873519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6582951/10000000) (δ := 2779/250000000) (ψ := 1151357/1000000) 220 193
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t246 : ((-556967502313/10000000000000 : ℚ) : ℝ) ≤ stT220 246 := by
  have hc : ((-873569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-556967502313/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-873569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c247 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((-10567/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4351711/10000000) (δ := 2779/250000000) (ψ := 1151357/1000000) 220 193
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t247 : ((-10760979177/1000000000000 : ℚ) : ℝ) ≤ stT220 247 := by
  have hc : ((-84561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10760979177/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-84561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c248 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((82329/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2129491/10000000) (δ := 2779/250000000) (ψ := 1151357/1000000) 220 193
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t248 : ((41819957/1000000000 : ℚ) : ℝ) ≤ stT220 248 := by
  have hc : ((329291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41819957/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((329291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c249 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((999439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20941/2500000) (δ := 2779/250000000) (ψ := 1151357/1000000) 220 193
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t249 : ((158334198659/2500000000000 : ℚ) : ℝ) ≤ stT220 249 := by
  have hc : ((999389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158334198659/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((999389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_c250 :
    |Real.cos (((220 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((609563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2288219/10000000) (δ := 2779/250000000) (ψ := 1151357/1000000) 220 193
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st220_t250 : ((77097908883/2000000000000 : ℚ) : ℝ) ≤ stT220 250 := by
  have hc : ((609513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((220 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st220_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77097908883/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((609513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st220_p1 : ((407199/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT220 (i+1) := by
  rw [Finset.sum_range_one]
  exact st220_t1

theorem st220_p2 : ((10119880676167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT220 (i+1))
      = (∑ i ∈ Finset.range 1, stT220 (i+1)) + stT220 2 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 1
    simpa using h
  have hprev := st220_p1
  have hstep := st220_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p3 : ((139180903699/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT220 (i+1))
      = (∑ i ∈ Finset.range 2, stT220 (i+1)) + stT220 3 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 2
    simpa using h
  have hprev := st220_p2
  have hstep := st220_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p4 : ((725442151991/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT220 (i+1))
      = (∑ i ∈ Finset.range 3, stT220 (i+1)) + stT220 4 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 3
    simpa using h
  have hprev := st220_p3
  have hstep := st220_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p5 : ((7963761778463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT220 (i+1))
      = (∑ i ∈ Finset.range 4, stT220 (i+1)) + stT220 5 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 4
    simpa using h
  have hprev := st220_p4
  have hstep := st220_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p6 : ((4110224425103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT220 (i+1))
      = (∑ i ∈ Finset.range 5, stT220 (i+1)) + stT220 6 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 5
    simpa using h
  have hprev := st220_p5
  have hstep := st220_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p7 : ((7712130666003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT220 (i+1))
      = (∑ i ∈ Finset.range 6, stT220 (i+1)) + stT220 7 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 6
    simpa using h
  have hprev := st220_p6
  have hstep := st220_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p8 : ((5235690624441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT220 (i+1))
      = (∑ i ∈ Finset.range 7, stT220 (i+1)) + stT220 8 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 7
    simpa using h
  have hprev := st220_p7
  have hstep := st220_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p9 : ((5247430623267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT220 (i+1))
      = (∑ i ∈ Finset.range 8, stT220 (i+1)) + stT220 9 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 8
    simpa using h
  have hprev := st220_p8
  have hstep := st220_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p10 : ((2309478300031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT220 (i+1))
      = (∑ i ∈ Finset.range 9, stT220 (i+1)) + stT220 10 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 9
    simpa using h
  have hprev := st220_p9
  have hstep := st220_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p11 : ((175996746027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT220 (i+1))
      = (∑ i ∈ Finset.range 10, stT220 (i+1)) + stT220 11 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 10
    simpa using h
  have hprev := st220_p10
  have hstep := st220_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p12 : ((164079011987/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT220 (i+1))
      = (∑ i ∈ Finset.range 11, stT220 (i+1)) + stT220 12 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 11
    simpa using h
  have hprev := st220_p11
  have hstep := st220_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p13 : ((2154483914497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT220 (i+1))
      = (∑ i ∈ Finset.range 12, stT220 (i+1)) + stT220 13 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 12
    simpa using h
  have hprev := st220_p12
  have hstep := st220_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p14 : ((2639621789961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT220 (i+1))
      = (∑ i ∈ Finset.range 13, stT220 (i+1)) + stT220 14 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 13
    simpa using h
  have hprev := st220_p13
  have hstep := st220_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p15 : ((952338454263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT220 (i+1))
      = (∑ i ∈ Finset.range 14, stT220 (i+1)) + stT220 15 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 14
    simpa using h
  have hprev := st220_p14
  have hstep := st220_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p16 : ((2941200954263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT220 (i+1))
      = (∑ i ∈ Finset.range 15, stT220 (i+1)) + stT220 16 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 15
    simpa using h
  have hprev := st220_p15
  have hstep := st220_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p17 : ((5348927041499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT220 (i+1))
      = (∑ i ∈ Finset.range 16, stT220 (i+1)) + stT220 17 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 16
    simpa using h
  have hprev := st220_p16
  have hstep := st220_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p18 : ((1537266780883/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT220 (i+1))
      = (∑ i ∈ Finset.range 17, stT220 (i+1)) + stT220 18 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 17
    simpa using h
  have hprev := st220_p17
  have hstep := st220_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p19 : ((2412634590551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT220 (i+1))
      = (∑ i ∈ Finset.range 18, stT220 (i+1)) + stT220 19 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 18
    simpa using h
  have hprev := st220_p18
  have hstep := st220_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p20 : ((9088719569/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT220 (i+1))
      = (∑ i ∈ Finset.range 19, stT220 (i+1)) + stT220 20 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 19
    simpa using h
  have hprev := st220_p19
  have hstep := st220_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p21 : ((7190178013241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT220 (i+1))
      = (∑ i ∈ Finset.range 20, stT220 (i+1)) + stT220 21 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 20
    simpa using h
  have hprev := st220_p20
  have hstep := st220_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p22 : ((4615308722299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT220 (i+1))
      = (∑ i ∈ Finset.range 21, stT220 (i+1)) + stT220 22 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 21
    simpa using h
  have hprev := st220_p21
  have hstep := st220_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p23 : ((3784390950669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT220 (i+1))
      = (∑ i ∈ Finset.range 22, stT220 (i+1)) + stT220 23 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 22
    simpa using h
  have hprev := st220_p22
  have hstep := st220_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p24 : ((4634159578969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT220 (i+1))
      = (∑ i ∈ Finset.range 23, stT220 (i+1)) + stT220 24 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 23
    simpa using h
  have hprev := st220_p23
  have hstep := st220_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p25 : ((7288628168093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT220 (i+1))
      = (∑ i ∈ Finset.range 24, stT220 (i+1)) + stT220 25 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 24
    simpa using h
  have hprev := st220_p24
  have hstep := st220_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p26 : ((8845923361041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT220 (i+1))
      = (∑ i ∈ Finset.range 25, stT220 (i+1)) + stT220 26 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 25
    simpa using h
  have hprev := st220_p25
  have hstep := st220_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p27 : ((9236379392541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT220 (i+1))
      = (∑ i ∈ Finset.range 26, stT220 (i+1)) + stT220 27 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 26
    simpa using h
  have hprev := st220_p26
  have hstep := st220_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p28 : ((3674789109759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT220 (i+1))
      = (∑ i ∈ Finset.range 27, stT220 (i+1)) + stT220 28 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 27
    simpa using h
  have hprev := st220_p27
  have hstep := st220_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p29 : ((1749084786217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT220 (i+1))
      = (∑ i ∈ Finset.range 28, stT220 (i+1)) + stT220 29 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 28
    simpa using h
  have hprev := st220_p28
  have hstep := st220_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p30 : ((8516379897569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT220 (i+1))
      = (∑ i ∈ Finset.range 29, stT220 (i+1)) + stT220 30 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 29
    simpa using h
  have hprev := st220_p29
  have hstep := st220_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p31 : ((10207360204963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT220 (i+1))
      = (∑ i ∈ Finset.range 30, stT220 (i+1)) + stT220 31 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 30
    simpa using h
  have hprev := st220_p30
  have hstep := st220_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p32 : ((11094317350037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT220 (i+1))
      = (∑ i ∈ Finset.range 31, stT220 (i+1)) + stT220 32 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 31
    simpa using h
  have hprev := st220_p31
  have hstep := st220_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p33 : ((11162277245077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT220 (i+1))
      = (∑ i ∈ Finset.range 32, stT220 (i+1)) + stT220 33 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 32
    simpa using h
  have hprev := st220_p32
  have hstep := st220_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p34 : ((10745587096657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT220 (i+1))
      = (∑ i ∈ Finset.range 33, stT220 (i+1)) + stT220 34 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 33
    simpa using h
  have hprev := st220_p33
  have hstep := st220_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p35 : ((2545674746719/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT220 (i+1))
      = (∑ i ∈ Finset.range 34, stT220 (i+1)) + stT220 35 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 34
    simpa using h
  have hprev := st220_p34
  have hstep := st220_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p36 : ((9764057236481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT220 (i+1))
      = (∑ i ∈ Finset.range 35, stT220 (i+1)) + stT220 36 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 35
    simpa using h
  have hprev := st220_p35
  have hstep := st220_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p37 : ((2441632037987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT220 (i+1))
      = (∑ i ∈ Finset.range 36, stT220 (i+1)) + stT220 37 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 36
    simpa using h
  have hprev := st220_p36
  have hstep := st220_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p38 : ((5212282330561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT220 (i+1))
      = (∑ i ∈ Finset.range 37, stT220 (i+1)) + stT220 38 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 37
    simpa using h
  have hprev := st220_p37
  have hstep := st220_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p39 : ((11759944944667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT220 (i+1))
      = (∑ i ∈ Finset.range 38, stT220 (i+1)) + stT220 39 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 38
    simpa using h
  have hprev := st220_p38
  have hstep := st220_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p40 : ((13327910483989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT220 (i+1))
      = (∑ i ∈ Finset.range 39, stT220 (i+1)) + stT220 40 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 39
    simpa using h
  have hprev := st220_p39
  have hstep := st220_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p41 : ((2839655801597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT220 (i+1))
      = (∑ i ∈ Finset.range 40, stT220 (i+1)) + stT220 41 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 40
    simpa using h
  have hprev := st220_p40
  have hstep := st220_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p42 : ((13610825904743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT220 (i+1))
      = (∑ i ∈ Finset.range 41, stT220 (i+1)) + stT220 42 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 41
    simpa using h
  have hprev := st220_p41
  have hstep := st220_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p43 : ((12089916192321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT220 (i+1))
      = (∑ i ∈ Finset.range 42, stT220 (i+1)) + stT220 43 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 42
    simpa using h
  have hprev := st220_p42
  have hstep := st220_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p44 : ((1434543126999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT220 (i+1))
      = (∑ i ∈ Finset.range 43, stT220 (i+1)) + stT220 44 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 43
    simpa using h
  have hprev := st220_p43
  have hstep := st220_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p45 : ((633116839953/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT220 (i+1))
      = (∑ i ∈ Finset.range 44, stT220 (i+1)) + stT220 45 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 44
    simpa using h
  have hprev := st220_p44
  have hstep := st220_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p46 : ((171157154139/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT220 (i+1))
      = (∑ i ∈ Finset.range 45, stT220 (i+1)) + stT220 46 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 45
    simpa using h
  have hprev := st220_p45
  have hstep := st220_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p47 : ((1266863941467/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT220 (i+1))
      = (∑ i ∈ Finset.range 46, stT220 (i+1)) + stT220 47 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 46
    simpa using h
  have hprev := st220_p46
  have hstep := st220_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p48 : ((5862735570487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT220 (i+1))
      = (∑ i ∈ Finset.range 47, stT220 (i+1)) + stT220 48 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 47
    simpa using h
  have hprev := st220_p47
  have hstep := st220_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p49 : ((2590740154501/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT220 (i+1))
      = (∑ i ∈ Finset.range 48, stT220 (i+1)) + stT220 49 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 48
    simpa using h
  have hprev := st220_p48
  have hstep := st220_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p50 : ((13328286198241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT220 (i+1))
      = (∑ i ∈ Finset.range 49, stT220 (i+1)) + stT220 50 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 49
    simpa using h
  have hprev := st220_p49
  have hstep := st220_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p51 : ((5966658232037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT220 (i+1))
      = (∑ i ∈ Finset.range 50, stT220 (i+1)) + stT220 51 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 50
    simpa using h
  have hprev := st220_p50
  have hstep := st220_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p52 : ((6316011065537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT220 (i+1))
      = (∑ i ∈ Finset.range 51, stT220 (i+1)) + stT220 52 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 51
    simpa using h
  have hprev := st220_p51
  have hstep := st220_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p53 : ((6657777725587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT220 (i+1))
      = (∑ i ∈ Finset.range 52, stT220 (i+1)) + stT220 53 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 52
    simpa using h
  have hprev := st220_p52
  have hstep := st220_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p54 : ((5979463483191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT220 (i+1))
      = (∑ i ∈ Finset.range 53, stT220 (i+1)) + stT220 54 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 53
    simpa using h
  have hprev := st220_p53
  have hstep := st220_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p55 : ((6441354863843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT220 (i+1))
      = (∑ i ∈ Finset.range 54, stT220 (i+1)) + stT220 55 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 54
    simpa using h
  have hprev := st220_p54
  have hstep := st220_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p56 : ((6486503298359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT220 (i+1))
      = (∑ i ∈ Finset.range 55, stT220 (i+1)) + stT220 56 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 55
    simpa using h
  have hprev := st220_p55
  have hstep := st220_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p57 : ((2400903997583/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT220 (i+1))
      = (∑ i ∈ Finset.range 56, stT220 (i+1)) + stT220 57 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 56
    simpa using h
  have hprev := st220_p56
  have hstep := st220_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p58 : ((2662928544911/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT220 (i+1))
      = (∑ i ∈ Finset.range 57, stT220 (i+1)) + stT220 58 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 57
    simpa using h
  have hprev := st220_p57
  have hstep := st220_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p59 : ((2441342961241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT220 (i+1))
      = (∑ i ∈ Finset.range 58, stT220 (i+1)) + stT220 59 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 58
    simpa using h
  have hprev := st220_p58
  have hstep := st220_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p60 : ((12781924928869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT220 (i+1))
      = (∑ i ∈ Finset.range 59, stT220 (i+1)) + stT220 60 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 59
    simpa using h
  have hprev := st220_p59
  have hstep := st220_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p61 : ((12824107932997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT220 (i+1))
      = (∑ i ∈ Finset.range 60, stT220 (i+1)) + stT220 61 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 60
    simpa using h
  have hprev := st220_p60
  have hstep := st220_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p62 : ((12250328649409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT220 (i+1))
      = (∑ i ∈ Finset.range 61, stT220 (i+1)) + stT220 62 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 61
    simpa using h
  have hprev := st220_p61
  have hstep := st220_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p63 : ((6597234806059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT220 (i+1))
      = (∑ i ∈ Finset.range 62, stT220 (i+1)) + stT220 63 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 62
    simpa using h
  have hprev := st220_p62
  have hstep := st220_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p64 : ((12043347441221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT220 (i+1))
      = (∑ i ∈ Finset.range 63, stT220 (i+1)) + stT220 64 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 63
    simpa using h
  have hprev := st220_p63
  have hstep := st220_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p65 : ((1659121145089/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT220 (i+1))
      = (∑ i ∈ Finset.range 64, stT220 (i+1)) + stT220 65 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 64
    simpa using h
  have hprev := st220_p64
  have hstep := st220_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p66 : ((12046545769547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT220 (i+1))
      = (∑ i ∈ Finset.range 65, stT220 (i+1)) + stT220 66 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 65
    simpa using h
  have hprev := st220_p65
  have hstep := st220_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p67 : ((13229352027833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT220 (i+1))
      = (∑ i ∈ Finset.range 66, stT220 (i+1)) + stT220 67 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 66
    simpa using h
  have hprev := st220_p66
  have hstep := st220_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p68 : ((378090736817/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT220 (i+1))
      = (∑ i ∈ Finset.range 67, stT220 (i+1)) + stT220 68 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 67
    simpa using h
  have hprev := st220_p67
  have hstep := st220_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p69 : ((6593849017181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT220 (i+1))
      = (∑ i ∈ Finset.range 68, stT220 (i+1)) + stT220 69 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 68
    simpa using h
  have hprev := st220_p68
  have hstep := st220_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p70 : ((6059545797311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT220 (i+1))
      = (∑ i ∈ Finset.range 69, stT220 (i+1)) + stT220 70 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 69
    simpa using h
  have hprev := st220_p69
  have hstep := st220_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p71 : ((527637931317/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT220 (i+1))
      = (∑ i ∈ Finset.range 70, stT220 (i+1)) + stT220 71 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 70
    simpa using h
  have hprev := st220_p70
  have hstep := st220_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p72 : ((12096006925869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT220 (i+1))
      = (∑ i ∈ Finset.range 71, stT220 (i+1)) + stT220 72 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 71
    simpa using h
  have hprev := st220_p71
  have hstep := st220_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p73 : ((3305838163281/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT220 (i+1))
      = (∑ i ∈ Finset.range 72, stT220 (i+1)) + stT220 73 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 72
    simpa using h
  have hprev := st220_p72
  have hstep := st220_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p74 : ((12069681416399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT220 (i+1))
      = (∑ i ∈ Finset.range 73, stT220 (i+1)) + stT220 74 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 73
    simpa using h
  have hprev := st220_p73
  have hstep := st220_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p75 : ((13221889573799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT220 (i+1))
      = (∑ i ∈ Finset.range 74, stT220 (i+1)) + stT220 75 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 74
    simpa using h
  have hprev := st220_p74
  have hstep := st220_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p76 : ((3030876306107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT220 (i+1))
      = (∑ i ∈ Finset.range 75, stT220 (i+1)) + stT220 76 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 75
    simpa using h
  have hprev := st220_p75
  have hstep := st220_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p77 : ((6544998693649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT220 (i+1))
      = (∑ i ∈ Finset.range 76, stT220 (i+1)) + stT220 77 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 76
    simpa using h
  have hprev := st220_p76
  have hstep := st220_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p78 : ((617610195511/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT220 (i+1))
      = (∑ i ∈ Finset.range 77, stT220 (i+1)) + stT220 78 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 77
    simpa using h
  have hprev := st220_p77
  have hstep := st220_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p79 : ((6379820333113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT220 (i+1))
      = (∑ i ∈ Finset.range 78, stT220 (i+1)) + stT220 79 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 78
    simpa using h
  have hprev := st220_p78
  have hstep := st220_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p80 : ((6381828320381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT220 (i+1))
      = (∑ i ∈ Finset.range 79, stT220 (i+1)) + stT220 80 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 79
    simpa using h
  have hprev := st220_p79
  have hstep := st220_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p81 : ((6159187031157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT220 (i+1))
      = (∑ i ∈ Finset.range 80, stT220 (i+1)) + stT220 81 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 80
    simpa using h
  have hprev := st220_p80
  have hstep := st220_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p82 : ((6575604339987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT220 (i+1))
      = (∑ i ∈ Finset.range 81, stT220 (i+1)) + stT220 82 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 81
    simpa using h
  have hprev := st220_p81
  have hstep := st220_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p83 : ((12085352323611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT220 (i+1))
      = (∑ i ∈ Finset.range 82, stT220 (i+1)) + stT220 83 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 82
    simpa using h
  have hprev := st220_p82
  have hstep := st220_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p84 : ((13138189925449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT220 (i+1))
      = (∑ i ∈ Finset.range 83, stT220 (i+1)) + stT220 84 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 83
    simpa using h
  have hprev := st220_p83
  have hstep := st220_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p85 : ((12385097993101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT220 (i+1))
      = (∑ i ∈ Finset.range 84, stT220 (i+1)) + stT220 85 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 84
    simpa using h
  have hprev := st220_p84
  have hstep := st220_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p86 : ((1259813982351/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT220 (i+1))
      = (∑ i ∈ Finset.range 85, stT220 (i+1)) + stT220 86 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 85
    simpa using h
  have hprev := st220_p85
  have hstep := st220_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p87 : ((6507431662619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT220 (i+1))
      = (∑ i ∈ Finset.range 86, stT220 (i+1)) + stT220 87 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 86
    simpa using h
  have hprev := st220_p86
  have hstep := st220_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p88 : ((6051413273487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT220 (i+1))
      = (∑ i ∈ Finset.range 87, stT220 (i+1)) + stT220 88 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 87
    simpa using h
  have hprev := st220_p87
  have hstep := st220_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p89 : ((1644524290717/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT220 (i+1))
      = (∑ i ∈ Finset.range 88, stT220 (i+1)) + stT220 89 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 88
    simpa using h
  have hprev := st220_p88
  have hstep := st220_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p90 : ((77611975133/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT220 (i+1))
      = (∑ i ∈ Finset.range 89, stT220 (i+1)) + stT220 90 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 89
    simpa using h
  have hprev := st220_p89
  have hstep := st220_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p91 : ((1560776989627/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT220 (i+1))
      = (∑ i ∈ Finset.range 90, stT220 (i+1)) + stT220 91 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 90
    simpa using h
  have hprev := st220_p90
  have hstep := st220_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p92 : ((1641897431803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT220 (i+1))
      = (∑ i ∈ Finset.range 91, stT220 (i+1)) + stT220 92 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 91
    simpa using h
  have hprev := st220_p91
  have hstep := st220_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p93 : ((1513462630987/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT220 (i+1))
      = (∑ i ∈ Finset.range 92, stT220 (i+1)) + stT220 93 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 92
    simpa using h
  have hprev := st220_p92
  have hstep := st220_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p94 : ((2585377103461/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT220 (i+1))
      = (∑ i ∈ Finset.range 93, stT220 (i+1)) + stT220 94 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 93
    simpa using h
  have hprev := st220_p93
  have hstep := st220_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p95 : ((3205007194619/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT220 (i+1))
      = (∑ i ∈ Finset.range 94, stT220 (i+1)) + stT220 95 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 94
    simpa using h
  have hprev := st220_p94
  have hstep := st220_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p96 : ((6068305375333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT220 (i+1))
      = (∑ i ∈ Finset.range 95, stT220 (i+1)) + stT220 96 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 95
    simpa using h
  have hprev := st220_p95
  have hstep := st220_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p97 : ((6575799674437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT220 (i+1))
      = (∑ i ∈ Finset.range 96, stT220 (i+1)) + stT220 97 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 96
    simpa using h
  have hprev := st220_p96
  have hstep := st220_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p98 : ((12531380559169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT220 (i+1))
      = (∑ i ∈ Finset.range 97, stT220 (i+1)) + stT220 98 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 97
    simpa using h
  have hprev := st220_p97
  have hstep := st220_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p99 : ((2457115080079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT220 (i+1))
      = (∑ i ∈ Finset.range 98, stT220 (i+1)) + stT220 99 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 98
    simpa using h
  have hprev := st220_p98
  have hstep := st220_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p100 : ((13209196476773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT220 (i+1))
      = (∑ i ∈ Finset.range 99, stT220 (i+1)) + stT220 100 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 99
    simpa using h
  have hprev := st220_p99
  have hstep := st220_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p101 : ((494628269773/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT220 (i+1))
      = (∑ i ∈ Finset.range 100, stT220 (i+1)) + stT220 101 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 100
    simpa using h
  have hprev := st220_p100
  have hstep := st220_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p102 : ((12402726360361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT220 (i+1))
      = (∑ i ∈ Finset.range 101, stT220 (i+1)) + stT220 102 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 101
    simpa using h
  have hprev := st220_p101
  have hstep := st220_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p103 : ((13208607242881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT220 (i+1))
      = (∑ i ∈ Finset.range 102, stT220 (i+1)) + stT220 103 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 102
    simpa using h
  have hprev := st220_p102
  have hstep := st220_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p104 : ((2461305134851/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT220 (i+1))
      = (∑ i ∈ Finset.range 103, stT220 (i+1)) + stT220 104 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 103
    simpa using h
  have hprev := st220_p103
  have hstep := st220_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p105 : ((2486889719611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT220 (i+1))
      = (∑ i ∈ Finset.range 104, stT220 (i+1)) + stT220 105 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 104
    simpa using h
  have hprev := st220_p104
  have hstep := st220_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p106 : ((1320995265189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT220 (i+1))
      = (∑ i ∈ Finset.range 105, stT220 (i+1)) + stT220 106 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 105
    simpa using h
  have hprev := st220_p105
  have hstep := st220_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p107 : ((6165547956069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT220 (i+1))
      = (∑ i ∈ Finset.range 106, stT220 (i+1)) + stT220 107 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 106
    simpa using h
  have hprev := st220_p106
  have hstep := st220_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p108 : ((6187611386319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT220 (i+1))
      = (∑ i ∈ Finset.range 107, stT220 (i+1)) + stT220 108 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 107
    simpa using h
  have hprev := st220_p107
  have hstep := st220_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p109 : ((330361676009/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT220 (i+1))
      = (∑ i ∈ Finset.range 108, stT220 (i+1)) + stT220 109 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 108
    simpa using h
  have hprev := st220_p108
  have hstep := st220_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p110 : ((3110951445143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT220 (i+1))
      = (∑ i ∈ Finset.range 109, stT220 (i+1)) + stT220 110 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 109
    simpa using h
  have hprev := st220_p109
  have hstep := st220_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p111 : ((6123189034549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT220 (i+1))
      = (∑ i ∈ Finset.range 110, stT220 (i+1)) + stT220 111 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 110
    simpa using h
  have hprev := st220_p110
  have hstep := st220_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p112 : ((13173731677807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT220 (i+1))
      = (∑ i ∈ Finset.range 111, stT220 (i+1)) + stT220 112 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 111
    simpa using h
  have hprev := st220_p111
  have hstep := st220_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p113 : ((791252421649/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT220 (i+1))
      = (∑ i ∈ Finset.range 112, stT220 (i+1)) + stT220 113 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 112
    simpa using h
  have hprev := st220_p112
  have hstep := st220_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p114 : ((302787382789/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT220 (i+1))
      = (∑ i ∈ Finset.range 113, stT220 (i+1)) + stT220 114 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 113
    simpa using h
  have hprev := st220_p113
  have hstep := st220_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p115 : ((813056416157/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT220 (i+1))
      = (∑ i ∈ Finset.range 114, stT220 (i+1)) + stT220 115 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 114
    simpa using h
  have hprev := st220_p114
  have hstep := st220_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p116 : ((12954182866517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT220 (i+1))
      = (∑ i ∈ Finset.range 115, stT220 (i+1)) + stT220 116 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 115
    simpa using h
  have hprev := st220_p115
  have hstep := st220_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p117 : ((12094409879531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT220 (i+1))
      = (∑ i ∈ Finset.range 116, stT220 (i+1)) + stT220 117 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 116
    simpa using h
  have hprev := st220_p116
  have hstep := st220_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p118 : ((12671864776529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT220 (i+1))
      = (∑ i ∈ Finset.range 117, stT220 (i+1)) + stT220 118 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 117
    simpa using h
  have hprev := st220_p117
  have hstep := st220_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p119 : ((2638932812563/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT220 (i+1))
      = (∑ i ∈ Finset.range 118, stT220 (i+1)) + stT220 119 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 118
    simpa using h
  have hprev := st220_p118
  have hstep := st220_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p120 : ((12333008777399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT220 (i+1))
      = (∑ i ∈ Finset.range 119, stT220 (i+1)) + stT220 120 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 119
    simpa using h
  have hprev := st220_p119
  have hstep := st220_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p121 : ((12258708769969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT220 (i+1))
      = (∑ i ∈ Finset.range 120, stT220 (i+1)) + stT220 121 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 120
    simpa using h
  have hprev := st220_p120
  have hstep := st220_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p122 : ((13152723457473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT220 (i+1))
      = (∑ i ∈ Finset.range 121, stT220 (i+1)) + stT220 122 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 121
    simpa using h
  have hprev := st220_p121
  have hstep := st220_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p123 : ((12815492565783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT220 (i+1))
      = (∑ i ∈ Finset.range 122, stT220 (i+1)) + stT220 123 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 122
    simpa using h
  have hprev := st220_p122
  have hstep := st220_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p124 : ((377224205037/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT220 (i+1))
      = (∑ i ∈ Finset.range 123, stT220 (i+1)) + stT220 124 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 123
    simpa using h
  have hprev := st220_p123
  have hstep := st220_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p125 : ((12706581762973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT220 (i+1))
      = (∑ i ∈ Finset.range 124, stT220 (i+1)) + stT220 125 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 124
    simpa using h
  have hprev := st220_p124
  have hstep := st220_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p126 : ((13208413288323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT220 (i+1))
      = (∑ i ∈ Finset.range 125, stT220 (i+1)) + stT220 126 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 125
    simpa using h
  have hprev := st220_p125
  have hstep := st220_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p127 : ((12401834170747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT220 (i+1))
      = (∑ i ∈ Finset.range 126, stT220 (i+1)) + stT220 127 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 126
    simpa using h
  have hprev := st220_p126
  have hstep := st220_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p128 : ((12161426561587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT220 (i+1))
      = (∑ i ∈ Finset.range 127, stT220 (i+1)) + stT220 128 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 127
    simpa using h
  have hprev := st220_p127
  have hstep := st220_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p129 : ((13033925217637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT220 (i+1))
      = (∑ i ∈ Finset.range 128, stT220 (i+1)) + stT220 129 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 128
    simpa using h
  have hprev := st220_p128
  have hstep := st220_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p130 : ((13039211246203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT220 (i+1))
      = (∑ i ∈ Finset.range 129, stT220 (i+1)) + stT220 130 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 129
    simpa using h
  have hprev := st220_p129
  have hstep := st220_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p131 : ((3042661126327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT220 (i+1))
      = (∑ i ∈ Finset.range 130, stT220 (i+1)) + stT220 131 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 130
    simpa using h
  have hprev := st220_p130
  have hstep := st220_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p132 : ((96508182551/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT220 (i+1))
      = (∑ i ∈ Finset.range 131, stT220 (i+1)) + stT220 132 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 131
    simpa using h
  have hprev := st220_p131
  have hstep := st220_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p133 : ((13181187620959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT220 (i+1))
      = (∑ i ∈ Finset.range 132, stT220 (i+1)) + stT220 133 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 132
    simpa using h
  have hprev := st220_p132
  have hstep := st220_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p134 : ((12862390588413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT220 (i+1))
      = (∑ i ∈ Finset.range 133, stT220 (i+1)) + stT220 134 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 133
    simpa using h
  have hprev := st220_p133
  have hstep := st220_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p135 : ((12084693780287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT220 (i+1))
      = (∑ i ∈ Finset.range 134, stT220 (i+1)) + stT220 135 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 134
    simpa using h
  have hprev := st220_p134
  have hstep := st220_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p136 : ((499698586739/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT220 (i+1))
      = (∑ i ∈ Finset.range 135, stT220 (i+1)) + stT220 136 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 135
    simpa using h
  have hprev := st220_p135
  have hstep := st220_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p137 : ((13226709326559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT220 (i+1))
      = (∑ i ∈ Finset.range 136, stT220 (i+1)) + stT220 137 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 136
    simpa using h
  have hprev := st220_p136
  have hstep := st220_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p138 : ((2554066344241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT220 (i+1))
      = (∑ i ∈ Finset.range 137, stT220 (i+1)) + stT220 138 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 137
    simpa using h
  have hprev := st220_p137
  have hstep := st220_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p139 : ((6031208533107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT220 (i+1))
      = (∑ i ∈ Finset.range 138, stT220 (i+1)) + stT220 139 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 138
    simpa using h
  have hprev := st220_p138
  have hstep := st220_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p140 : ((626619472869/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT220 (i+1))
      = (∑ i ∈ Finset.range 139, stT220 (i+1)) + stT220 140 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 139
    simpa using h
  have hprev := st220_p139
  have hstep := st220_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p141 : ((13234574119029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT220 (i+1))
      = (∑ i ∈ Finset.range 140, stT220 (i+1)) + stT220 141 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 140
    simpa using h
  have hprev := st220_p140
  have hstep := st220_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p142 : ((12782573071007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT220 (i+1))
      = (∑ i ∈ Finset.range 141, stT220 (i+1)) + stT220 142 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 141
    simpa using h
  have hprev := st220_p141
  have hstep := st220_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p143 : ((482642399951/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT220 (i+1))
      = (∑ i ∈ Finset.range 142, stT220 (i+1)) + stT220 143 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 142
    simpa using h
  have hprev := st220_p142
  have hstep := st220_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p144 : ((6234271168891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT220 (i+1))
      = (∑ i ∈ Finset.range 143, stT220 (i+1)) + stT220 144 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 143
    simpa using h
  have hprev := st220_p143
  have hstep := st220_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p145 : ((6607081900387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT220 (i+1))
      = (∑ i ∈ Finset.range 144, stT220 (i+1)) + stT220 145 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 144
    simpa using h
  have hprev := st220_p144
  have hstep := st220_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p146 : ((1289407559379/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT220 (i+1))
      = (∑ i ∈ Finset.range 145, stT220 (i+1)) + stT220 146 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 145
    simpa using h
  have hprev := st220_p145
  have hstep := st220_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p147 : ((12113209326327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT220 (i+1))
      = (∑ i ∈ Finset.range 146, stT220 (i+1)) + stT220 147 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 146
    simpa using h
  have hprev := st220_p146
  have hstep := st220_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p148 : ((12315502049727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT220 (i+1))
      = (∑ i ∈ Finset.range 147, stT220 (i+1)) + stT220 148 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 147
    simpa using h
  have hprev := st220_p147
  have hstep := st220_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p149 : ((1640538132291/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT220 (i+1))
      = (∑ i ∈ Finset.range 148, stT220 (i+1)) + stT220 149 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 148
    simpa using h
  have hprev := st220_p148
  have hstep := st220_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p150 : ((13075162553389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT220 (i+1))
      = (∑ i ∈ Finset.range 149, stT220 (i+1)) + stT220 150 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 149
    simpa using h
  have hprev := st220_p149
  have hstep := st220_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p151 : ((6131151043319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT220 (i+1))
      = (∑ i ∈ Finset.range 150, stT220 (i+1)) + stT220 151 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 150
    simpa using h
  have hprev := st220_p150
  have hstep := st220_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p152 : ((6063536269331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT220 (i+1))
      = (∑ i ∈ Finset.range 151, stT220 (i+1)) + stT220 152 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 151
    simpa using h
  have hprev := st220_p151
  have hstep := st220_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p153 : ((6450207138377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT220 (i+1))
      = (∑ i ∈ Finset.range 152, stT220 (i+1)) + stT220 153 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 152
    simpa using h
  have hprev := st220_p152
  have hstep := st220_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p154 : ((165482853073/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT220 (i+1))
      = (∑ i ∈ Finset.range 153, stT220 (i+1)) + stT220 154 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 153
    simpa using h
  have hprev := st220_p153
  have hstep := st220_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p155 : ((157084224109/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT220 (i+1))
      = (∑ i ∈ Finset.range 154, stT220 (i+1)) + stT220 155 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 154
    simpa using h
  have hprev := st220_p154
  have hstep := st220_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p156 : ((300729689033/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT220 (i+1))
      = (∑ i ∈ Finset.range 155, stT220 (i+1)) + stT220 156 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 155
    simpa using h
  have hprev := st220_p155
  have hstep := st220_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p157 : ((3131144274853/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT220 (i+1))
      = (∑ i ∈ Finset.range 156, stT220 (i+1)) + stT220 157 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 156
    simpa using h
  have hprev := st220_p156
  have hstep := st220_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p158 : ((3306079303583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT220 (i+1))
      = (∑ i ∈ Finset.range 157, stT220 (i+1)) + stT220 158 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 157
    simpa using h
  have hprev := st220_p157
  have hstep := st220_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p159 : ((3245024609259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT220 (i+1))
      = (∑ i ∈ Finset.range 158, stT220 (i+1)) + stT220 159 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 158
    simpa using h
  have hprev := st220_p158
  have hstep := st220_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p160 : ((762207311911/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT220 (i+1))
      = (∑ i ∈ Finset.range 159, stT220 (i+1)) + stT220 160 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 159
    simpa using h
  have hprev := st220_p159
  have hstep := st220_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p161 : ((6066702283319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT220 (i+1))
      = (∑ i ∈ Finset.range 160, stT220 (i+1)) + stT220 161 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 160
    simpa using h
  have hprev := st220_p160
  have hstep := st220_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p162 : ((6443435323341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT220 (i+1))
      = (∑ i ∈ Finset.range 161, stT220 (i+1)) + stT220 162 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 161
    simpa using h
  have hprev := st220_p161
  have hstep := st220_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p163 : ((6632574989991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT220 (i+1))
      = (∑ i ∈ Finset.range 162, stT220 (i+1)) + stT220 163 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 162
    simpa using h
  have hprev := st220_p162
  have hstep := st220_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p164 : ((12682870803193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT220 (i+1))
      = (∑ i ∈ Finset.range 163, stT220 (i+1)) + stT220 164 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 163
    simpa using h
  have hprev := st220_p163
  have hstep := st220_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p165 : ((6021937465749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT220 (i+1))
      = (∑ i ∈ Finset.range 164, stT220 (i+1)) + stT220 165 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 164
    simpa using h
  have hprev := st220_p164
  have hstep := st220_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p166 : ((192531609857/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT220 (i+1))
      = (∑ i ∈ Finset.range 165, stT220 (i+1)) + stT220 166 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 165
    simpa using h
  have hprev := st220_p165
  have hstep := st220_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p167 : ((523620235133/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT220 (i+1))
      = (∑ i ∈ Finset.range 166, stT220 (i+1)) + stT220 167 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 166
    simpa using h
  have hprev := st220_p166
  have hstep := st220_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p168 : ((2639664276349/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT220 (i+1))
      = (∑ i ∈ Finset.range 167, stT220 (i+1)) + stT220 168 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 167
    simpa using h
  have hprev := st220_p167
  have hstep := st220_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p169 : ((6245700200219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT220 (i+1))
      = (∑ i ∈ Finset.range 168, stT220 (i+1)) + stT220 169 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 168
    simpa using h
  have hprev := st220_p168
  have hstep := st220_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p170 : ((12010139833483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT220 (i+1))
      = (∑ i ∈ Finset.range 169, stT220 (i+1)) + stT220 170 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 169
    simpa using h
  have hprev := st220_p169
  have hstep := st220_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p171 : ((6224738890727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT220 (i+1))
      = (∑ i ∈ Finset.range 170, stT220 (i+1)) + stT220 171 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 170
    simpa using h
  have hprev := st220_p170
  have hstep := st220_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p172 : ((1317224242327/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT220 (i+1))
      = (∑ i ∈ Finset.range 171, stT220 (i+1)) + stT220 172 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 171
    simpa using h
  have hprev := st220_p171
  have hstep := st220_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p173 : ((3287609545269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT220 (i+1))
      = (∑ i ∈ Finset.range 172, stT220 (i+1)) + stT220 173 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 172
    simpa using h
  have hprev := st220_p172
  have hstep := st220_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p174 : ((6210305862591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT220 (i+1))
      = (∑ i ∈ Finset.range 173, stT220 (i+1)) + stT220 174 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 173
    simpa using h
  have hprev := st220_p173
  have hstep := st220_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p175 : ((6001829715539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT220 (i+1))
      = (∑ i ∈ Finset.range 174, stT220 (i+1)) + stT220 175 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 174
    simpa using h
  have hprev := st220_p174
  have hstep := st220_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p176 : ((6235666726699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT220 (i+1))
      = (∑ i ∈ Finset.range 175, stT220 (i+1)) + stT220 176 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 175
    simpa using h
  have hprev := st220_p175
  have hstep := st220_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p177 : ((3294659776053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT220 (i+1))
      = (∑ i ∈ Finset.range 176, stT220 (i+1)) + stT220 177 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 176
    simpa using h
  have hprev := st220_p176
  have hstep := st220_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p178 : ((1646042847891/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT220 (i+1))
      = (∑ i ∈ Finset.range 177, stT220 (i+1)) + stT220 178 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 177
    simpa using h
  have hprev := st220_p177
  have hstep := st220_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p179 : ((3114975690389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT220 (i+1))
      = (∑ i ∈ Finset.range 178, stT220 (i+1)) + stT220 179 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 178
    simpa using h
  have hprev := st220_p178
  have hstep := st220_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p180 : ((374910587479/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT220 (i+1))
      = (∑ i ∈ Finset.range 179, stT220 (i+1)) + stT220 180 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 179
    simpa using h
  have hprev := st220_p179
  have hstep := st220_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p181 : ((6192509298497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT220 (i+1))
      = (∑ i ∈ Finset.range 180, stT220 (i+1)) + stT220 181 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 180
    simpa using h
  have hprev := st220_p180
  have hstep := st220_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p182 : ((3278209411903/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT220 (i+1))
      = (∑ i ∈ Finset.range 181, stT220 (i+1)) + stT220 182 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 181
    simpa using h
  have hprev := st220_p181
  have hstep := st220_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p183 : ((6620725876259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT220 (i+1))
      = (∑ i ∈ Finset.range 182, stT220 (i+1)) + stT220 183 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 182
    simpa using h
  have hprev := st220_p182
  have hstep := st220_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p184 : ((3152924923437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT220 (i+1))
      = (∑ i ∈ Finset.range 183, stT220 (i+1)) + stT220 184 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 183
    simpa using h
  have hprev := st220_p183
  have hstep := st220_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p185 : ((6012211592809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT220 (i+1))
      = (∑ i ∈ Finset.range 184, stT220 (i+1)) + stT220 185 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 184
    simpa using h
  have hprev := st220_p184
  have hstep := st220_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p186 : ((12213447502443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT220 (i+1))
      = (∑ i ∈ Finset.range 185, stT220 (i+1)) + stT220 186 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 185
    simpa using h
  have hprev := st220_p185
  have hstep := st220_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p187 : ((12938477364651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT220 (i+1))
      = (∑ i ∈ Finset.range 186, stT220 (i+1)) + stT220 187 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 186
    simpa using h
  have hprev := st220_p186
  have hstep := st220_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p188 : ((13305775870911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT220 (i+1))
      = (∑ i ∈ Finset.range 187, stT220 (i+1)) + stT220 188 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 187
    simpa using h
  have hprev := st220_p187
  have hstep := st220_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p189 : ((6435880053711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT220 (i+1))
      = (∑ i ∈ Finset.range 188, stT220 (i+1)) + stT220 189 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 188
    simpa using h
  have hprev := st220_p188
  have hstep := st220_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p190 : ((152065715411/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT220 (i+1))
      = (∑ i ∈ Finset.range 189, stT220 (i+1)) + stT220 190 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 189
    simpa using h
  have hprev := st220_p189
  have hstep := st220_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p191 : ((2406211300241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT220 (i+1))
      = (∑ i ∈ Finset.range 190, stT220 (i+1)) + stT220 191 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 190
    simpa using h
  have hprev := st220_p190
  have hstep := st220_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p192 : ((2524635806819/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT220 (i+1))
      = (∑ i ∈ Finset.range 191, stT220 (i+1)) + stT220 192 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 191
    simpa using h
  have hprev := st220_p191
  have hstep := st220_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p193 : ((165532562939/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT220 (i+1))
      = (∑ i ∈ Finset.range 192, stT220 (i+1)) + stT220 193 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 192
    simpa using h
  have hprev := st220_p192
  have hstep := st220_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p194 : ((1646313090063/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT220 (i+1))
      = (∑ i ∈ Finset.range 193, stT220 (i+1)) + stT220 194 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 193
    simpa using h
  have hprev := st220_p193
  have hstep := st220_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p195 : ((12495144541269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT220 (i+1))
      = (∑ i ∈ Finset.range 194, stT220 (i+1)) + stT220 195 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 194
    simpa using h
  have hprev := st220_p194
  have hstep := st220_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p196 : ((11990425767953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT220 (i+1))
      = (∑ i ∈ Finset.range 195, stT220 (i+1)) + stT220 196 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 195
    simpa using h
  have hprev := st220_p195
  have hstep := st220_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p197 : ((12224616081893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT220 (i+1))
      = (∑ i ∈ Finset.range 196, stT220 (i+1)) + stT220 197 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 196
    simpa using h
  have hprev := st220_p196
  have hstep := st220_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p198 : ((3232494273783/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT220 (i+1))
      = (∑ i ∈ Finset.range 197, stT220 (i+1)) + stT220 198 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 197
    simpa using h
  have hprev := st220_p197
  have hstep := st220_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p199 : ((2664202431799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT220 (i+1))
      = (∑ i ∈ Finset.range 198, stT220 (i+1)) + stT220 199 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 198
    simpa using h
  have hprev := st220_p198
  have hstep := st220_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p200 : ((648531148141/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT220 (i+1))
      = (∑ i ∈ Finset.range 199, stT220 (i+1)) + stT220 200 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 199
    simpa using h
  have hprev := st220_p199
  have hstep := st220_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p201 : ((3066487818399/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT220 (i+1))
      = (∑ i ∈ Finset.range 200, stT220 (i+1)) + stT220 201 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 200
    simpa using h
  have hprev := st220_p200
  have hstep := st220_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p202 : ((5984979074483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT220 (i+1))
      = (∑ i ∈ Finset.range 201, stT220 (i+1)) + stT220 202 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 201
    simpa using h
  have hprev := st220_p201
  have hstep := st220_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p203 : ((774747124483/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT220 (i+1))
      = (∑ i ∈ Finset.range 202, stT220 (i+1)) + stT220 203 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 202
    simpa using h
  have hprev := st220_p202
  have hstep := st220_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p204 : ((3271706909707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT220 (i+1))
      = (∑ i ∈ Finset.range 203, stT220 (i+1)) + stT220 204 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 203
    simpa using h
  have hprev := st220_p203
  have hstep := st220_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p205 : ((3328679940097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT220 (i+1))
      = (∑ i ∈ Finset.range 204, stT220 (i+1)) + stT220 205 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 204
    simpa using h
  have hprev := st220_p204
  have hstep := st220_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p206 : ((200716360019/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT220 (i+1))
      = (∑ i ∈ Finset.range 205, stT220 (i+1)) + stT220 206 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 205
    simpa using h
  have hprev := st220_p205
  have hstep := st220_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p207 : ((12169498334561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT220 (i+1))
      = (∑ i ∈ Finset.range 206, stT220 (i+1)) + stT220 207 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 206
    simpa using h
  have hprev := st220_p206
  have hstep := st220_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p208 : ((2395856760621/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT220 (i+1))
      = (∑ i ∈ Finset.range 207, stT220 (i+1)) + stT220 208 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 207
    simpa using h
  have hprev := st220_p207
  have hstep := st220_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p209 : ((12464398740727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT220 (i+1))
      = (∑ i ∈ Finset.range 208, stT220 (i+1)) + stT220 209 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 208
    simpa using h
  have hprev := st220_p208
  have hstep := st220_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p210 : ((6565913079201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT220 (i+1))
      = (∑ i ∈ Finset.range 209, stT220 (i+1)) + stT220 210 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 209
    simpa using h
  have hprev := st220_p209
  have hstep := st220_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p211 : ((6657381065421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT220 (i+1))
      = (∑ i ∈ Finset.range 210, stT220 (i+1)) + stT220 211 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 210
    simpa using h
  have hprev := st220_p210
  have hstep := st220_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p212 : ((1283604395657/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT220 (i+1))
      = (∑ i ∈ Finset.range 211, stT220 (i+1)) + stT220 212 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 211
    simpa using h
  have hprev := st220_p211
  have hstep := st220_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p213 : ((6084880345729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT220 (i+1))
      = (∑ i ∈ Finset.range 212, stT220 (i+1)) + stT220 213 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 212
    simpa using h
  have hprev := st220_p212
  have hstep := st220_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p214 : ((5982333559111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT220 (i+1))
      = (∑ i ∈ Finset.range 213, stT220 (i+1)) + stT220 214 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 213
    simpa using h
  have hprev := st220_p213
  have hstep := st220_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p215 : ((6207414084913/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT220 (i+1))
      = (∑ i ∈ Finset.range 214, stT220 (i+1)) + stT220 215 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 214
    simpa using h
  have hprev := st220_p214
  have hstep := st220_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p216 : ((3271318960257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT220 (i+1))
      = (∑ i ∈ Finset.range 215, stT220 (i+1)) + stT220 216 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 215
    simpa using h
  have hprev := st220_p215
  have hstep := st220_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p217 : ((1667411305107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT220 (i+1))
      = (∑ i ∈ Finset.range 216, stT220 (i+1)) + stT220 217 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 216
    simpa using h
  have hprev := st220_p216
  have hstep := st220_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p218 : ((6470688055569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT220 (i+1))
      = (∑ i ∈ Finset.range 217, stT220 (i+1)) + stT220 218 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 217
    simpa using h
  have hprev := st220_p217
  have hstep := st220_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p219 : ((3066746889981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT220 (i+1))
      = (∑ i ∈ Finset.range 218, stT220 (i+1)) + stT220 219 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 218
    simpa using h
  have hprev := st220_p218
  have hstep := st220_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p220 : ((2985263077981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT220 (i+1))
      = (∑ i ∈ Finset.range 219, stT220 (i+1)) + stT220 220 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 219
    simpa using h
  have hprev := st220_p219
  have hstep := st220_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p221 : ((3064876499869/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT220 (i+1))
      = (∑ i ∈ Finset.range 220, stT220 (i+1)) + stT220 221 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 220
    simpa using h
  have hprev := st220_p220
  have hstep := st220_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p222 : ((646412090547/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT220 (i+1))
      = (∑ i ∈ Finset.range 221, stT220 (i+1)) + stT220 222 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 221
    simpa using h
  have hprev := st220_p221
  have hstep := st220_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p223 : ((3335538634109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT220 (i+1))
      = (∑ i ∈ Finset.range 222, stT220 (i+1)) + stT220 223 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 222
    simpa using h
  have hprev := st220_p222
  have hstep := st220_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p224 : ((41041375477/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT220 (i+1))
      = (∑ i ∈ Finset.range 223, stT220 (i+1)) + stT220 224 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 223
    simpa using h
  have hprev := st220_p223
  have hstep := st220_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p225 : ((1249120649829/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT220 (i+1))
      = (∑ i ∈ Finset.range 224, stT220 (i+1)) + stT220 225 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 224
    simpa using h
  have hprev := st220_p224
  have hstep := st220_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p226 : ((5991788980039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT220 (i+1))
      = (∑ i ∈ Finset.range 225, stT220 (i+1)) + stT220 226 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 225
    simpa using h
  have hprev := st220_p225
  have hstep := st220_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p227 : ((2410389480517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT220 (i+1))
      = (∑ i ∈ Finset.range 226, stT220 (i+1)) + stT220 227 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 226
    simpa using h
  have hprev := st220_p226
  have hstep := st220_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p228 : ((12632941443597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT220 (i+1))
      = (∑ i ∈ Finset.range 227, stT220 (i+1)) + stT220 228 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 227
    simpa using h
  have hprev := st220_p227
  have hstep := st220_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p229 : ((13224363641327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT220 (i+1))
      = (∑ i ∈ Finset.range 228, stT220 (i+1)) + stT220 229 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 228
    simpa using h
  have hprev := st220_p228
  have hstep := st220_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p230 : ((13322805119047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT220 (i+1))
      = (∑ i ∈ Finset.range 229, stT220 (i+1)) + stT220 230 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 229
    simpa using h
  have hprev := st220_p229
  have hstep := st220_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p231 : ((12848708594119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT220 (i+1))
      = (∑ i ∈ Finset.range 230, stT220 (i+1)) + stT220 231 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 230
    simpa using h
  have hprev := st220_p230
  have hstep := st220_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p232 : ((3050808066593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT220 (i+1))
      = (∑ i ∈ Finset.range 231, stT220 (i+1)) + stT220 232 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 231
    simpa using h
  have hprev := st220_p231
  have hstep := st220_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p233 : ((1490482918867/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT220 (i+1))
      = (∑ i ∈ Finset.range 232, stT220 (i+1)) + stT220 233 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 232
    simpa using h
  have hprev := st220_p232
  have hstep := st220_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p234 : ((1529776884057/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT220 (i+1))
      = (∑ i ∈ Finset.range 233, stT220 (i+1)) + stT220 234 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 233
    simpa using h
  have hprev := st220_p233
  have hstep := st220_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p235 : ((402653974397/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT220 (i+1))
      = (∑ i ∈ Finset.range 234, stT220 (i+1)) + stT220 235 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 234
    simpa using h
  have hprev := st220_p234
  have hstep := st220_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p236 : ((416777770811/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT220 (i+1))
      = (∑ i ∈ Finset.range 235, stT220 (i+1)) + stT220 236 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 235
    simpa using h
  have hprev := st220_p235
  have hstep := st220_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p237 : ((6615822992061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT220 (i+1))
      = (∑ i ∈ Finset.range 236, stT220 (i+1)) + stT220 237 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 236
    simpa using h
  have hprev := st220_p236
  have hstep := st220_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p238 : ((6328599910437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT220 (i+1))
      = (∑ i ∈ Finset.range 237, stT220 (i+1)) + stT220 238 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 237
    simpa using h
  have hprev := st220_p237
  have hstep := st220_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p239 : ((3018026825991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT220 (i+1))
      = (∑ i ∈ Finset.range 238, stT220 (i+1)) + stT220 239 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 238
    simpa using h
  have hprev := st220_p238
  have hstep := st220_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p240 : ((746032689441/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT220 (i+1))
      = (∑ i ∈ Finset.range 239, stT220 (i+1)) + stT220 240 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 239
    simpa using h
  have hprev := st220_p239
  have hstep := st220_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p241 : ((77206480483/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT220 (i+1))
      = (∑ i ∈ Finset.range 240, stT220 (i+1)) + stT220 241 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 240
    simpa using h
  have hprev := st220_p240
  have hstep := st220_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p242 : ((162440306019/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT220 (i+1))
      = (∑ i ∈ Finset.range 241, stT220 (i+1)) + stT220 242 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 241
    simpa using h
  have hprev := st220_p241
  have hstep := st220_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p243 : ((668401899001/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT220 (i+1))
      = (∑ i ∈ Finset.range 242, stT220 (i+1)) + stT220 243 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 242
    simpa using h
  have hprev := st220_p242
  have hstep := st220_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p244 : ((2637813700321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT220 (i+1))
      = (∑ i ∈ Finset.range 243, stT220 (i+1)) + stT220 244 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 243
    simpa using h
  have hprev := st220_p243
  have hstep := st220_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p245 : ((12597582119711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT220 (i+1))
      = (∑ i ∈ Finset.range 244, stT220 (i+1)) + stT220 245 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 244
    simpa using h
  have hprev := st220_p244
  have hstep := st220_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p246 : ((6020307308699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT220 (i+1))
      = (∑ i ∈ Finset.range 245, stT220 (i+1)) + stT220 246 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 245
    simpa using h
  have hprev := st220_p245
  have hstep := st220_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p247 : ((2983251206407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT220 (i+1))
      = (∑ i ∈ Finset.range 246, stT220 (i+1)) + stT220 247 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 246
    simpa using h
  have hprev := st220_p246
  have hstep := st220_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p248 : ((3087801098907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT220 (i+1))
      = (∑ i ∈ Finset.range 247, stT220 (i+1)) + stT220 248 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 247
    simpa using h
  have hprev := st220_p247
  have hstep := st220_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p249 : ((1623067648783/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT220 (i+1))
      = (∑ i ∈ Finset.range 248, stT220 (i+1)) + stT220 249 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 248
    simpa using h
  have hprev := st220_p248
  have hstep := st220_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_p250 : ((13370030734679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT220 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT220 (i+1))
      = (∑ i ∈ Finset.range 249, stT220 (i+1)) + stT220 250 := by
    have h := Finset.sum_range_succ (fun i => stT220 (i+1)) 249
    simpa using h
  have hprev := st220_p249
  have hstep := st220_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st220_s250 :
    |Real.sin (((220 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))
      - ((396369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 2288219/10000000) (δ := 2779/250000000) (ψ := 1151357/1000000) 220 193
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 220`** (evaluated boundary). -/
theorem station_220_sign : hardyG ((((220:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 220 250 (by norm_num) (by norm_num)
    ((1151357/1000000 : ℚ) : ℝ)
  have hchain := st220_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT220 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((220 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((1151357/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st220_c250
  have hsinb := abs_le.mp st220_s250
  have hbdy_lo : ((-27625388177981/484002500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((220 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ))) / 2
          - ((((220:ℕ)):ℝ))
            * Real.sin (((220 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((1151357/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((220:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((220:ℝ) * Real.log (250:ℝ) - ((1151357/1000000 : ℚ) : ℝ))) / 2
        - ((220:ℝ)) * Real.sin ((220:ℝ) * Real.log (250:ℝ) - ((1151357/1000000 : ℚ) : ℝ))
        ≥ ((-349436333/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((220:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-349436333/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-349436333/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-349436333/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((220:ℕ)):ℝ))+1) * (((((220:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((335046016767/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((13370030734679/10000000000000 : ℚ) : ℝ) + ((-27625388177981/484002500000000 : ℚ) : ℝ)
      - ((335046016767/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((1151357/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((220:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((1151357/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((220:ℕ)):ℝ)))).re
      - Real.sin ((1151357/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((220:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((220:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((220:ℕ)):ℝ))
      = (((((220:ℕ)):ℝ)) * (Real.log ((((220:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((220:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_220
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
  have hθwin : |(((1151357/1000000 : ℚ) : ℝ) + ((45:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((220:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((220:ℕ)):ℝ)))
    (φ := ((1151357/1000000 : ℚ) : ℝ) + ((45:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((1151357/1000000 : ℚ) : ℝ) + ((45:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((1151357/1000000 : ℚ)) : ℝ) - Real.pi) + ((45:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((1151357/1000000 : ℚ)) : ℝ) - Real.pi) 45).1,
    (cos_sin_shift ((((1151357/1000000 : ℚ)) : ℝ) - Real.pi) 45).2]
  exact cos_sin_flip ((1151357/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_220_sign
end AxiomAudit
