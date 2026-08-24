import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 95` (rung-109; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT95 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((95 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))

theorem st95_c1 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((845179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 704871/5000000) (δ := 21/100000000) (ψ := -563897/1000000) 95 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t1 : ((845129/1000000 : ℚ) : ℝ) ≤ stT95 1 := by
  have hc : ((845129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((845129/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((845129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c2 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-904993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6755399/10000000) (δ := 729/100000000) (ψ := -563897/1000000) 95 11
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t2 : ((-1599905148981/2500000000000 : ℚ) : ℝ) ≤ stT95 2 := by
  have hc : ((-905043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1599905148981/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-905043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c3 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-306287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -941043/2000000) (δ := 103/12500000) (ψ := -563897/1000000) 95 17
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t3 : ((-1768637588511/10000000000000 : ℚ) : ℝ) ≤ stT95 3 := by
  have hc : ((-306337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1768637588511/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-306337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c4 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((475403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 24607/312500) (δ := 557/100000000) (ψ := -563897/1000000) 95 21
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t4 : ((237689/500000 : ℚ) : ℝ) ≤ stT95 4 := by
  have hc : ((237689/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237689/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((237689/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c5 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-13877/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 208129/312500) (δ := 211/25000000) (ψ := -563897/1000000) 95 24
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t5 : ((-248253300513/625000000000 : ℚ) : ℝ) ≤ stT95 5 := by
  have hc : ((-444089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248253300513/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-444089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c6 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((422093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354701/1250000) (δ := 651/100000000) (ψ := -563897/1000000) 95 27
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t6 : ((861491475363/5000000000000 : ℚ) : ℝ) ≤ stT95 6 := by
  have hc : ((422043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((861491475363/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((422043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c7 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-997453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -959437/1250000) (δ := 13/2500000) (ψ := -563897/1000000) 95 30
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t7 : ((-754041445287/2000000000000 : ℚ) : ℝ) ≤ stT95 7 := by
  have hc : ((-997503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-754041445287/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-997503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c8 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-245477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1844429/2500000) (δ := 559/100000000) (ψ := -563897/1000000) 95 32
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t8 : ((-867936473893/2500000000000 : ℚ) : ℝ) ≤ stT95 8 := by
  have hc : ((-490979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-867936473893/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-490979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c9 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-374929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4887791/10000000) (δ := 141/20000000) (ψ := -563897/1000000) 95 33
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t9 : ((-624965124993/5000000000000 : ℚ) : ℝ) ≤ stT95 9 := by
  have hc : ((-374979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-624965124993/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-374979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c10 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((412101/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1505013/10000000) (δ := 857/100000000) (ψ := -563897/1000000) 95 35
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t10 : ((325774614263/1250000000000 : ℚ) : ℝ) ≤ stT95 10 := by
  have hc : ((103019/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325774614263/1250000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((103019/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c11 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-140847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677899/1250000) (δ := 687/100000000) (ψ := -563897/1000000) 95 36
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t11 : ((-424707450483/2500000000000 : ℚ) : ℝ) ≤ stT95 11 := by
  have hc : ((-281719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424707450483/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-281719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c12 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-53137/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5327533/10000000) (δ := 63/12500000) (ψ := -563897/1000000) 95 38
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t12 : ((-2396996481/15625000000 : ℚ) : ℝ) ≤ stT95 12 := by
  have hc : ((-26571/50000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2396996481/15625000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-26571/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c13 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((172349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2025353/10000000) (δ := 53/10000000) (ψ := -563897/1000000) 95 39
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t13 : ((1911901131/10000000000 : ℚ) : ℝ) ≤ stT95 13 := by
  have hc : ((344673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1911901131/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((344673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c14 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((15603/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132673/10000000) (δ := 693/100000000) (ψ := -563897/1000000) 95 40
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t14 : ((333589416463/1250000000000 : ℚ) : ℝ) ≤ stT95 14 := by
  have hc : ((499271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333589416463/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((499271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c15 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((976317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 545171/10000000) (δ := 119/12500000) (ψ := -563897/1000000) 95 41
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t15 : ((630177419699/2500000000000 : ℚ) : ℝ) ≤ stT95 15 := by
  have hc : ((976267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((630177419699/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((976267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c16 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((49891/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82553/5000000) (δ := 771/100000000) (ψ := -563897/1000000) 95 42
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t16 : ((99777/400000 : ℚ) : ℝ) ≤ stT95 16 := by
  have hc : ((99777/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99777/400000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((99777/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c17 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((35881/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1144509/10000000) (δ := 541/100000000) (ψ := -563897/1000000) 95 43
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t17 : ((21754836981/100000000000 : ℚ) : ℝ) ≤ stT95 17 := by
  have hc : ((35879/40000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21754836981/100000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((35879/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c18 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((128471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3277349/10000000) (δ := 543/100000000) (ψ := -563897/1000000) 95 44
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t18 : ((75687511953/1250000000000 : ℚ) : ℝ) ≤ stT95 18 := by
  have hc : ((64223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75687511953/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((64223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c19 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-96893/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1536087/2500000) (δ := 357/50000000) (ψ := -563897/1000000) 95 45
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t19 : ((-444604379163/2500000000000 : ℚ) : ℝ) ≤ stT95 19 := by
  have hc : ((-387597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444604379163/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-387597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c20 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-29901/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 603781/1000000) (δ := 171/25000000) (ψ := -563897/1000000) 95 45
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t20 : ((-16716285351/100000000000 : ℚ) : ℝ) ≤ stT95 20 := by
  have hc : ((-29903/40000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16716285351/100000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-29903/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c21 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((719993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1917511/10000000) (δ := 299/50000000) (ψ := -563897/1000000) 95 46
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t21 : ((785521887927/5000000000000 : ℚ) : ℝ) ≤ stT95 21 := by
  have hc : ((719943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((785521887927/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((719943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c22 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((28529/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2741949/10000000) (δ := 97/20000000) (ψ := -563897/1000000) 95 47
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t22 : ((486538921449/5000000000000 : ℚ) : ℝ) ≤ stT95 22 := by
  have hc : ((228207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486538921449/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((228207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c23 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-999881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1563069/2000000) (δ := 101/12500000) (ψ := -563897/1000000) 95 47
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t23 : ((-417000224999/2000000000000 : ℚ) : ℝ) ≤ stT95 23 := by
  have hc : ((-999931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-417000224999/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-999931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c24 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((25297/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221529/1000000) (δ := 677/100000000) (ψ := -563897/1000000) 95 48
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t24 : ((10326638219/80000000000 : ℚ) : ℝ) ≤ stT95 24 := by
  have hc : ((5059/8000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10326638219/80000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((5059/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c25 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((51793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75949/200000) (δ := 373/50000000) (ψ := -563897/1000000) 95 49
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t25 : ((51743/5000000 : ℚ) : ℝ) ≤ stT95 25 := by
  have hc : ((51743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51743/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((51743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c26 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-74267/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 551747/1000000) (δ := 149/25000000) (ψ := -563897/1000000) 95 49
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t26 : ((-291323751033/2500000000000 : ℚ) : ℝ) ≤ stT95 26 := by
  have hc : ((-297093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291323751033/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-297093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c27 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((35277/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -613583/5000000) (δ := 597/100000000) (ψ := -563897/1000000) 95 50
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t27 : ((5430939/32000000 : ℚ) : ℝ) ≤ stT95 27 := by
  have hc : ((1411/1600 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5430939/32000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((1411/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c28 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-492141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148203/200000) (δ := 433/50000000) (ψ := -563897/1000000) 95 50
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t28 : ((-465053313309/2500000000000 : ℚ) : ℝ) ≤ stT95 28 := by
  have hc : ((-246083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465053313309/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-246083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c29 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((499947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291/80000) (δ := 137/20000000) (ψ := -563897/1000000) 95 51
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t29 : ((464165828833/2500000000000 : ℚ) : ℝ) ≤ stT95 29 := by
  have hc : ((249961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((464165828833/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((249961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c30 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-497811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -761997/1000000) (δ := 749/100000000) (ψ := -563897/1000000) 95 52
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t30 : ((-113615011789/625000000000 : ℚ) : ℝ) ≤ stT95 30 := by
  have hc : ((-124459/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113615011789/625000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-124459/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c31 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((997753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 167613/10000000) (δ := 467/50000000) (ψ := -563897/1000000) 95 52
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t31 : ((1791927466259/10000000000000 : ℚ) : ℝ) ≤ stT95 31 := by
  have hc : ((997703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1791927466259/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((997703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c32 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-499147/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7707929/10000000) (δ := 59/6250000) (ψ := -563897/1000000) 95 52
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t32 : ((-220604947231/1250000000000 : ℚ) : ℝ) ≤ stT95 32 := by
  have hc : ((-124793/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220604947231/1250000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-124793/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c33 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((961961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138353/2000000) (δ := 29/5000000) (ψ := -563897/1000000) 95 53
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t33 : ((209308947867/1250000000000 : ℚ) : ℝ) ≤ stT95 33 := by
  have hc : ((961911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209308947867/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((961911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c34 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-417609/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6398313/10000000) (δ := 753/100000000) (ψ := -563897/1000000) 95 53
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t34 : ((-179059115781/1250000000000 : ℚ) : ℝ) ≤ stT95 34 := by
  have hc : ((-208817/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179059115781/1250000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-208817/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c35 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((565263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242511/1000000) (δ := 7/1250000) (ψ := -563897/1000000) 95 54
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t35 : ((238846013901/2500000000000 : ℚ) : ℝ) ≤ stT95 35 := by
  have hc : ((565213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238846013901/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((565213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c36 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-6749/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4265473/10000000) (δ := 623/100000000) (ψ := -563897/1000000) 95 54
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t36 : ((-22505004501/1000000000000 : ℚ) : ℝ) ≤ stT95 36 := by
  have hc : ((-13503/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22505004501/1000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-13503/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c37 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-392453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4935233/10000000) (δ := 13/1562500) (ψ := -563897/1000000) 95 55
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t37 : ((-64527100697/1000000000000 : ℚ) : ℝ) ≤ stT95 37 := by
  have hc : ((-392503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64527100697/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-392503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c38 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((847579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55939/400000) (δ := 541/100000000) (ψ := -563897/1000000) 95 55
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t38 : ((687436704603/5000000000000 : ℚ) : ℝ) ≤ stT95 38 := by
  have hc : ((847529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((687436704603/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((847529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c39 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-124181/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7567653/10000000) (δ := 271/50000000) (ψ := -563897/1000000) 95 55
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t39 : ((-397717616109/2500000000000 : ℚ) : ℝ) ≤ stT95 39 := by
  have hc : ((-496749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397717616109/2500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-496749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c40 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((329641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2127331/10000000) (δ := 241/50000000) (ψ := -563897/1000000) 95 56
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t40 : ((16286511969/156250000000 : ℚ) : ℝ) ≤ stT95 40 := by
  have hc : ((20601/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16286511969/156250000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((20601/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c41 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((75857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 747433/2000000) (δ := 311/50000000) (ψ := -563897/1000000) 95 56
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t41 : ((118390596759/10000000000000 : ℚ) : ℝ) ≤ stT95 41 := by
  have hc : ((75807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118390596759/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((75807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c42 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-12509/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -624763/1000000) (δ := 801/100000000) (ψ := -563897/1000000) 95 57
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t42 : ((-308848284821/2500000000000 : ℚ) : ℝ) ≤ stT95 42 := by
  have hc : ((-400313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308848284821/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-400313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c43 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((241361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -659137/10000000) (δ := 831/100000000) (ψ := -563897/1000000) 95 57
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t43 : ((147221136909/1000000000000 : ℚ) : ℝ) ≤ stT95 43 := by
  have hc : ((482697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147221136909/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((482697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c44 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-171239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2400437/5000000) (δ := 641/100000000) (ψ := -563897/1000000) 95 57
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t44 : ((-1008555633/19531250000 : ℚ) : ℝ) ≤ stT95 44 := by
  have hc : ((-5352/15625 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1008555633/19531250000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-5352/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c45 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-305419/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2784893/5000000) (δ := 843/100000000) (ψ := -563897/1000000) 95 58
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t45 : ((-14229032379/156250000000 : ℚ) : ℝ) ≤ stT95 45 := by
  have hc : ((-76361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14229032379/156250000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-76361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c46 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((990227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87449/2500000) (δ := 893/100000000) (ψ := -563897/1000000) 95 58
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t46 : ((1459935782163/10000000000000 : ℚ) : ℝ) ≤ stT95 46 := by
  have hc : ((990177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1459935782163/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((990177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c47 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-326289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 594741/1250000) (δ := 19/2000000) (ψ := -563897/1000000) 95 58
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t47 : ((-9520287647/200000000000 : ℚ) : ℝ) ≤ stT95 47 := by
  have hc : ((-326339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9520287647/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-326339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c48 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-723697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5949851/10000000) (δ := 879/100000000) (ψ := -563897/1000000) 95 59
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t48 : ((-65289940617/625000000000 : ℚ) : ℝ) ≤ stT95 48 := by
  have hc : ((-723747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65289940617/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-723747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c49 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((912637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105277/1000000) (δ := 457/50000000) (ψ := -563897/1000000) 95 59
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t49 : ((1303695323177/10000000000000 : ℚ) : ℝ) ≤ stT95 49 := by
  have hc : ((912587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1303695323177/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((912587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c50 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((72583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3745373/10000000) (δ := 919/100000000) (ψ := -563897/1000000) 95 59
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t50 : ((102577111529/10000000000000 : ℚ) : ℝ) ≤ stT95 50 := by
  have hc : ((72533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102577111529/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((72533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c51 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-971857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3629733/5000000) (δ := 81/12500000) (ψ := -563897/1000000) 95 60
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t51 : ((-1360942905867/10000000000000 : ℚ) : ℝ) ≤ stT95 51 := by
  have hc : ((-971907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1360942905867/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-971907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c52 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((97937/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2647671/10000000) (δ := 399/50000000) (ψ := -563897/1000000) 95 60
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t52 : ((543201069/8000000000 : ℚ) : ℝ) ≤ stT95 52 := by
  have hc : ((97927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543201069/8000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((97927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c53 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((731341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75051/400000) (δ := 429/50000000) (ψ := -563897/1000000) 95 60
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t53 : ((200900994811/2000000000000 : ℚ) : ℝ) ≤ stT95 53 := by
  have hc : ((731291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200900994811/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((731291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c54 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-816583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6315657/10000000) (δ := 33/6250000) (ψ := -563897/1000000) 95 60
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t54 : ((-277824263031/2500000000000 : ℚ) : ℝ) ≤ stT95 54 := by
  have hc : ((-816633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277824263031/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-816633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c55 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-214307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2517193/5000000) (δ := 157/20000000) (ψ := -563897/1000000) 95 61
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t55 : ((-180628293/3125000000 : ℚ) : ℝ) ≤ stT95 55 := by
  have hc : ((-53583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180628293/3125000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-53583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c56 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((190949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -754991/10000000) (δ := 167/20000000) (ψ := -563897/1000000) 95 61
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t56 : ((127576465667/1000000000000 : ℚ) : ℝ) ≤ stT95 56 := by
  have hc : ((190939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127576465667/1000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((190939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c57 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((190167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3448659/10000000) (δ := 127/20000000) (ψ := -563897/1000000) 95 61
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t57 : ((62954012561/2500000000000 : ℚ) : ℝ) ≤ stT95 57 := by
  have hc : ((190117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62954012561/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((190117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c58 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-496983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3789599/5000000) (δ := 429/50000000) (ψ := -563897/1000000) 95 61
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t58 : ((-8157547619/62500000000 : ℚ) : ℝ) ≤ stT95 58 := by
  have hc : ((-31063/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8157547619/62500000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-31063/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c59 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-14177/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2034419/5000000) (δ := 567/100000000) (ψ := -563897/1000000) 95 62
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t59 : ((-3694633631/500000000000 : ℚ) : ℝ) ≤ stT95 59 := by
  have hc : ((-28379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3694633631/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-28379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c60 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((249881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77147/10000000) (δ := 9/1562500) (ψ := -563897/1000000) 95 62
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t60 : ((322578734289/2500000000000 : ℚ) : ℝ) ≤ stT95 60 := by
  have hc : ((499737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322578734289/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((499737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c61 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((15683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1924281/5000000) (δ := 293/50000000) (ψ := -563897/1000000) 95 62
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t61 : ((626500067/156250000000 : ℚ) : ℝ) ≤ stT95 61 := by
  have hc : ((7829/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((626500067/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((7829/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c62 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-62397/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1927609/2500000) (δ := 199/25000000) (ψ := -563897/1000000) 95 62
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t62 : ((-316993134201/2500000000000 : ℚ) : ℝ) ≤ stT95 62 := by
  have hc : ((-499201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316993134201/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-499201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c63 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-107971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2098723/5000000) (δ := 353/50000000) (ψ := -563897/1000000) 95 63
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t63 : ((-68046856761/5000000000000 : ℚ) : ℝ) ≤ stT95 63 := by
  have hc : ((-108021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68046856761/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-108021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c64 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((983323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114303/2500000) (δ := 757/100000000) (ψ := -563897/1000000) 95 63
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t64 : ((983273/8000000 : ℚ) : ℝ) ≤ stT95 64 := by
  have hc : ((983273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((983273/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((983273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c65 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((69277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3225033/10000000) (δ := 657/100000000) (ψ := -563897/1000000) 95 63
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t65 : ((171824029563/5000000000000 : ℚ) : ℝ) ≤ stT95 65 := by
  have hc : ((138529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171824029563/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((138529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c66 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-184121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6851057/10000000) (δ := 293/50000000) (ψ := -563897/1000000) 95 63
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t66 : ((-45329921973/400000000000 : ℚ) : ℝ) ≤ stT95 66 := by
  have hc : ((-184131/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45329921973/400000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-184131/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c67 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-258511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528541/1000000) (δ := 393/50000000) (ψ := -563897/1000000) 95 64
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t67 : ((-7896303463/125000000000 : ℚ) : ℝ) ≤ stT95 67 := by
  have hc : ((-32317/62500 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7896303463/125000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-32317/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c68 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((760489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1766827/10000000) (δ := 229/25000000) (ψ := -563897/1000000) 95 64
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t68 : ((461083822821/5000000000000 : ℚ) : ℝ) ≤ stT95 68 := by
  have hc : ((760439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461083822821/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((760439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c69 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((31099/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 425097/2500000) (δ := 229/25000000) (ψ := -563897/1000000) 95 64
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t69 : ((18718186113/200000000000 : ℚ) : ℝ) ≤ stT95 69 := by
  have hc : ((31097/40000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18718186113/200000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((31097/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c70 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-114621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5117713/10000000) (δ := 283/50000000) (ψ := -563897/1000000) 95 64
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t70 : ((-274026567143/5000000000000 : ℚ) : ℝ) ≤ stT95 70 := by
  have hc : ((-229267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274026567143/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-229267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c71 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-484079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36107/50000) (δ := 349/50000000) (ψ := -563897/1000000) 95 65
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t71 : ((-35907869583/312500000000 : ℚ) : ℝ) ≤ stT95 71 := by
  have hc : ((-60513/62500 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35907869583/312500000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-60513/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c72 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((10929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3899667/10000000) (δ := 157/20000000) (ψ := -563897/1000000) 95 65
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t72 : ((12821021169/10000000000000 : ℚ) : ℝ) ≤ stT95 72 := by
  have hc : ((10879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12821021169/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((10879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c73 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((242259/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -623753/10000000) (δ := 23/4000000) (ψ := -563897/1000000) 95 65
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t73 : ((567055936623/5000000000000 : ℚ) : ℝ) ≤ stT95 73 := by
  have hc : ((484493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((567055936623/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((484493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c74 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((1259/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2607589/10000000) (δ := 429/50000000) (ψ := -563897/1000000) 95 65
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t74 : ((2926823949/50000000000 : ℚ) : ℝ) ≤ stT95 74 := by
  have hc : ((10071/20000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2926823949/50000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((10071/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c75 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-679753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5795557/10000000) (δ := 33/4000000) (ψ := -563897/1000000) 95 65
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t75 : ((-784969203903/10000000000000 : ℚ) : ℝ) ≤ stT95 75 := by
  have hc : ((-679803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-784969203903/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-679803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c76 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-906901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353333/2000000) (δ := 287/50000000) (ψ := -563897/1000000) 95 66
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t76 : ((-1040344446129/10000000000000 : ℚ) : ℝ) ≤ stT95 76 := by
  have hc : ((-906951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1040344446129/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-906951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c77 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((5289/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1831023/5000000) (δ := 191/25000000) (ψ := -563897/1000000) 95 66
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t77 : ((2409808733/200000000000 : ℚ) : ℝ) ≤ stT95 77 := by
  have hc : ((10573/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2409808733/200000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((10573/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c78 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((121447/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -597487/10000000) (δ := 11/1562500) (ψ := -563897/1000000) 95 66
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t78 : ((550018272351/5000000000000 : ℚ) : ℝ) ≤ stT95 78 := by
  have hc : ((485763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((550018272351/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((485763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c79 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((564299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2428031/10000000) (δ := 121/25000000) (ψ := -563897/1000000) 95 66
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t79 : ((634829214663/10000000000000 : ℚ) : ℝ) ≤ stT95 79 := by
  have hc : ((564249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634829214663/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((564249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c80 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-14021/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1353873/2500000) (δ := 161/25000000) (ψ := -563897/1000000) 95 66
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t80 : ((-31354704513/500000000000 : ℚ) : ℝ) ≤ stT95 80 := by
  have hc : ((-56089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31354704513/500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-56089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c81 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-979113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7342123/10000000) (δ := 49/10000000) (ψ := -563897/1000000) 95 67
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t81 : ((-135994969907/1250000000000 : ℚ) : ℝ) ≤ stT95 81 := by
  have hc : ((-979163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135994969907/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-979163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c82 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-12441/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553497/1250000) (δ := 533/100000000) (ψ := -563897/1000000) 95 67
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t82 : ((-27484492687/1250000000000 : ℚ) : ℝ) ≤ stT95 82 := by
  have hc : ((-99553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27484492687/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-99553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c83 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((32563/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1549153/10000000) (δ := 913/100000000) (ψ := -563897/1000000) 95 67
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t83 : ((17870160581/200000000000 : ℚ) : ℝ) ≤ stT95 83 := by
  have hc : ((32561/40000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17870160581/200000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((32561/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c84 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((868773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1295193/10000000) (δ := 973/100000000) (ψ := -563897/1000000) 95 67
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t84 : ((947854109347/10000000000000 : ℚ) : ℝ) ≤ stT95 84 := by
  have hc : ((868723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((947854109347/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((868723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c85 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-71493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1026469/2500000) (δ := 1/200000) (ψ := -563897/1000000) 95 67
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t85 : ((-77599329579/10000000000000 : ℚ) : ℝ) ≤ stT95 85 := by
  have hc : ((-71543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77599329579/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-71543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c86 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-925623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3441843/5000000) (δ := 9/1000000) (ψ := -563897/1000000) 95 67
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t86 : ((-124772389343/1250000000000 : ℚ) : ℝ) ≤ stT95 86 := by
  have hc : ((-925673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124772389343/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-925673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c87 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-379129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3039291/5000000) (δ := 793/100000000) (ψ := -563897/1000000) 95 68
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t87 : ((-203247966201/2500000000000 : ℚ) : ℝ) ≤ stT95 87 := by
  have hc : ((-189577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203247966201/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-189577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c88 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((111597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3364267/10000000) (δ := 843/100000000) (ψ := -563897/1000000) 95 68
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t88 : ((29734021679/1250000000000 : ℚ) : ℝ) ≤ stT95 88 := by
  have hc : ((27893/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29734021679/1250000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((27893/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c89 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((963169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -340311/5000000) (δ := 33/5000000) (ψ := -563897/1000000) 95 68
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t89 : ((1020903250643/10000000000000 : ℚ) : ℝ) ≤ stT95 89 := by
  have hc : ((963119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1020903250643/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((963119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c90 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((704403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493259/2500000) (δ := 63/10000000) (ψ := -563897/1000000) 95 68
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t90 : ((185613215619/2500000000000 : ℚ) : ℝ) ≤ stT95 90 := by
  have hc : ((704353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185613215619/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((704353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c91 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-264951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4597373/10000000) (δ := 101/10000000) (ψ := -563897/1000000) 95 68
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t91 : ((-55559314657/2000000000000 : ℚ) : ℝ) ≤ stT95 91 := by
  have hc : ((-265001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55559314657/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-265001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c92 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-482627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7193027/10000000) (δ := 9/1250000) (ψ := -563897/1000000) 95 68
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t92 : ((-125799985899/1250000000000 : ℚ) : ℝ) ≤ stT95 92 := by
  have hc : ((-120663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125799985899/1250000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-120663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c93 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-180751/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371709/625000) (δ := 861/100000000) (ψ := -563897/1000000) 95 69
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t93 : ((-46860768213/625000000000 : ℚ) : ℝ) ≤ stT95 93 := by
  have hc : ((-361527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46860768213/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-361527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c94 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((12901/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3407213/10000000) (δ := 751/100000000) (ψ := -563897/1000000) 95 69
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t94 : ((106425113043/5000000000000 : ℚ) : ℝ) ≤ stT95 94 := by
  have hc : ((103183/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106425113043/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((103183/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c95 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((187349/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -446981/5000000) (δ := 841/100000000) (ψ := -563897/1000000) 95 69
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t95 : ((96102846271/1000000000000 : ℚ) : ℝ) ≤ stT95 95 := by
  have hc : ((187339/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96102846271/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((187339/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c96 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((803771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 398243/2500000) (δ := 851/100000000) (ψ := -563897/1000000) 95 69
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t96 : ((41014686351/500000000000 : ℚ) : ℝ) ≤ stT95 96 := by
  have hc : ((803721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41014686351/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((803721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c97 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-10167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2027067/5000000) (δ := 731/100000000) (ψ := -563897/1000000) 95 69
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t97 : ((-10333186419/2000000000000 : ℚ) : ℝ) ≤ stT95 97 := by
  have hc : ((-10177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10333186419/2000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-10177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c98 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-854831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6490053/10000000) (δ := 741/100000000) (ψ := -563897/1000000) 95 69
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t98 : ((-863560606793/10000000000000 : ℚ) : ℝ) ≤ stT95 98 := by
  have hc : ((-854881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-863560606793/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-854881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c99 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-182707/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3403361/5000000) (δ := 481/100000000) (ψ := -563897/1000000) 95 70
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t99 : ((-91818764123/1000000000000 : ℚ) : ℝ) ≤ stT95 99 := by
  have hc : ((-182717/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91818764123/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-182717/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c100 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-195837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -552471/1250000) (δ := 391/50000000) (ψ := -563897/1000000) 95 70
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t100 : ((-195887/10000000 : ℚ) : ℝ) ≤ stT95 100 := by
  have hc : ((-195887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-195887/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-195887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c101 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((680299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -514141/2500000) (δ := 811/100000000) (ψ := -563897/1000000) 95 70
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t101 : ((676872924213/10000000000000 : ℚ) : ℝ) ≤ stT95 101 := by
  have hc : ((680249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((676872924213/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((680249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c102 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((62099/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70839/2500000) (δ := 861/100000000) (ψ := -563897/1000000) 95 70
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t102 : ((491872354749/5000000000000 : ℚ) : ℝ) ≤ stT95 102 := by
  have hc : ((496767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((491872354749/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((496767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c103 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((253033/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 20316/78125) (δ := 411/50000000) (ψ := -563897/1000000) 95 70
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t103 : ((15581007477/312500000000 : ℚ) : ℝ) ≤ stT95 103 := by
  have hc : ((15813/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15581007477/312500000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((15813/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c104 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-377657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 305947/625000) (δ := 233/25000000) (ψ := -563897/1000000) 95 70
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t104 : ((-370372307767/10000000000000 : ℚ) : ℝ) ≤ stT95 104 := by
  have hc : ((-377707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370372307767/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-377707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c105 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-962579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 895987/1250000) (δ := 511/100000000) (ψ := -563897/1000000) 95 70
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t105 : ((-939430603729/10000000000000 : ℚ) : ℝ) ≤ stT95 105 := by
  have hc : ((-962629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-939430603729/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-962629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c106 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-16207/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1257773/2000000) (δ := 441/50000000) (ψ := -563897/1000000) 95 71
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t106 : ((-491956359/6250000000 : ℚ) : ℝ) ≤ stT95 106 := by
  have hc : ((-1013/1250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-491956359/6250000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-1013/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c107 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-527/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2029401/5000000) (δ := 651/100000000) (ψ := -563897/1000000) 95 71
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t107 : ((-203981507/40000000000 : ℚ) : ℝ) ≤ stT95 107 := by
  have hc : ((-211/4000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203981507/40000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-211/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c108 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((46163/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -462371/2500000) (δ := 731/100000000) (ψ := -563897/1000000) 95 71
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t108 : ((1421354871/20000000000 : ℚ) : ℝ) ≤ stT95 108 := by
  have hc : ((369279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1421354871/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((369279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c109 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((198159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21217/625000) (δ := 381/50000000) (ψ := -563897/1000000) 95 71
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t109 : ((94896132037/1000000000000 : ℚ) : ℝ) ≤ stT95 109 := by
  have hc : ((198149/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94896132037/1000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((198149/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c110 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((537459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2508437/10000000) (δ := 153/25000000) (ψ := -563897/1000000) 95 71
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t110 : ((256199529979/5000000000000 : ℚ) : ℝ) ≤ stT95 110 := by
  have hc : ((537409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256199529979/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((537409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c111 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-36021/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4657773/10000000) (δ := 951/100000000) (ψ := -563897/1000000) 95 71
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t111 : ((-68391105111/2500000000000 : ℚ) : ℝ) ≤ stT95 111 := by
  have hc : ((-144109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68391105111/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-144109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c112 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-227609/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848479/1250000) (δ := 331/50000000) (ψ := -563897/1000000) 95 71
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t112 : ((-26885285851/312500000000 : ℚ) : ℝ) ≤ stT95 112 := by
  have hc : ((-455243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26885285851/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-455243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c113 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-913907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3404503/5000000) (δ := 39/5000000) (ψ := -563897/1000000) 95 72
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t113 : ((-859778542997/10000000000000 : ℚ) : ℝ) ≤ stT95 113 := by
  have hc : ((-913957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-859778542997/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-913957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c114 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-155287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2358241/5000000) (δ := 13/2500000) (ψ := -563897/1000000) 95 72
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t114 : ((-4545720151/156250000000 : ℚ) : ℝ) ≤ stT95 114 := by
  have hc : ((-9707/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4545720151/156250000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-9707/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c115 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((24579/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2642233/10000000) (δ := 71/10000000) (ψ := -563897/1000000) 95 72
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t115 : ((5729421139/125000000000 : ℚ) : ℝ) ≤ stT95 115 := by
  have hc : ((49153/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5729421139/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((49153/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c116 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((972659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -585943/10000000) (δ := 843/100000000) (ψ := -563897/1000000) 95 72
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t116 : ((225761028471/2500000000000 : ℚ) : ℝ) ≤ stT95 116 := by
  have hc : ((972609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225761028471/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((972609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c117 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((835871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181587/1250000) (δ := 13/2000000) (ψ := -563897/1000000) 95 72
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t117 : ((1545433029/20000000000 : ℚ) : ℝ) ≤ stT95 117 := by
  have hc : ((835821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1545433029/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((835821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c118 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((45053/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694797/2000000) (δ := 37/5000000) (ψ := -563897/1000000) 95 72
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t118 : ((41463113247/2500000000000 : ℚ) : ℝ) ≤ stT95 118 := by
  have hc : ((90081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41463113247/2500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((90081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c119 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-290717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 684777/1250000) (δ := 853/100000000) (ψ := -563897/1000000) 95 72
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t119 : ((-133261450329/2500000000000 : ℚ) : ℝ) ≤ stT95 119 := by
  have hc : ((-145371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133261450329/2500000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-145371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c120 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-493981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1866419/2500000) (δ := 11/2000000) (ψ := -563897/1000000) 95 72
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t120 : ((-225481875613/2500000000000 : ℚ) : ℝ) ≤ stT95 120 := by
  have hc : ((-247003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225481875613/2500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-247003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c121 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-806219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3135661/5000000) (δ := 539/100000000) (ψ := -563897/1000000) 95 73
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t121 : ((-732971891479/10000000000000 : ℚ) : ℝ) ≤ stT95 121 := by
  have hc : ((-806269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-732971891479/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-806269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c122 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-31041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2158289/5000000) (δ := 529/100000000) (ψ := -563897/1000000) 95 73
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t122 : ((-14056135629/1000000000000 : ℚ) : ℝ) ≤ stT95 122 := by
  have hc : ((-31051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14056135629/1000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-31051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c123 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((290387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37153/156250) (δ := 257/50000000) (ψ := -563897/1000000) 95 73
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t123 : ((130905207089/2500000000000 : ℚ) : ℝ) ≤ stT95 123 := by
  have hc : ((145181/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130905207089/2500000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((145181/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c124 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((196701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90941/2000000) (δ := 297/50000000) (ψ := -563897/1000000) 95 73
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t124 : ((88316815983/1000000000000 : ℚ) : ℝ) ≤ stT95 124 := by
  have hc : ((196691/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88316815983/1000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((196691/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c125 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((417909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181617/1250000) (δ := 619/100000000) (ψ := -563897/1000000) 95 73
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t125 : ((93441683117/1250000000000 : ℚ) : ℝ) ≤ stT95 125 := by
  have hc : ((104471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93441683117/1250000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((104471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c126 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((230553/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 104543/312500) (δ := 919/100000000) (ψ := -563897/1000000) 95 73
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t126 : ((20534820761/1000000000000 : ℚ) : ℝ) ≤ stT95 126 := by
  have hc : ((230503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20534820761/1000000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((230503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c127 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-123861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652857/1250000) (δ := 49/6250000) (ψ := -563897/1000000) 95 73
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t127 : ((-219840034679/5000000000000 : ℚ) : ℝ) ≤ stT95 127 := by
  have hc : ((-247747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219840034679/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-247747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c128 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-953139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7085611/10000000) (δ := 73/12500000) (ψ := -563897/1000000) 95 73
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t128 : ((-210627126519/2500000000000 : ℚ) : ℝ) ≤ stT95 128 := by
  have hc : ((-953189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210627126519/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-953189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c129 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-908149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3387047/5000000) (δ := 469/50000000) (ψ := -563897/1000000) 95 74
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t129 : ((-799624717749/10000000000000 : ℚ) : ℝ) ≤ stT95 129 := by
  have hc : ((-908199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-799624717749/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-908199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c130 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-197123/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1235027/2500000) (δ := 249/50000000) (ψ := -563897/1000000) 95 74
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t130 : ((-43227606933/1250000000000 : ℚ) : ℝ) ≤ stT95 130 := by
  have hc : ((-49287/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43227606933/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-49287/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c131 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((317153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195011/625000) (δ := 3/390625) (ψ := -563897/1000000) 95 74
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t131 : ((34631769939/1250000000000 : ℚ) : ℝ) ≤ stT95 131 := by
  have hc : ((317103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34631769939/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((317103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c132 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((432503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1314083/10000000) (δ := 187/25000000) (ψ := -563897/1000000) 95 74
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t132 : ((47052957683/625000000000 : ℚ) : ℝ) ≤ stT95 132 := by
  have hc : ((216239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47052957683/625000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((216239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c133 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((245437/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239189/5000000) (δ := 177/25000000) (ψ := -563897/1000000) 95 74
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t133 : ((425619585541/5000000000000 : ℚ) : ℝ) ≤ stT95 133 := by
  have hc : ((490849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425619585541/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((490849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c134 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((123857/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2257413/10000000) (δ := 479/50000000) (ψ := -563897/1000000) 95 74
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t134 : ((26746865049/500000000000 : ℚ) : ℝ) ≤ stT95 134 := by
  have hc : ((123847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26746865049/500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((123847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c135 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-19241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 201161/500000) (δ := 29/4000000) (ψ := -563897/1000000) 95 74
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t135 : ((-8290766679/2500000000000 : ℚ) : ℝ) ≤ stT95 135 := by
  have hc : ((-9633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8290766679/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-9633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c136 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-336997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1443999/2500000) (δ := 163/20000000) (ψ := -563897/1000000) 95 74
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t136 : ((-144497002923/2500000000000 : ℚ) : ℝ) ≤ stT95 136 := by
  have hc : ((-168511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144497002923/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-168511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c137 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-123859/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 751593/1000000) (δ := 91/12500000) (ψ := -563897/1000000) 95 74
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t137 : ((-211650534519/2500000000000 : ℚ) : ℝ) ≤ stT95 137 := by
  have hc : ((-495461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211650534519/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-495461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c138 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-13274/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6464753/10000000) (δ := 157/20000000) (ψ := -563897/1000000) 95 75
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t138 : ((-361608014801/5000000000000 : ℚ) : ℝ) ≤ stT95 138 := by
  have hc : ((-424793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361608014801/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-424793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c139 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-80817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -593743/1250000) (δ := 329/50000000) (ψ := -563897/1000000) 95 75
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t139 : ((-137117385551/5000000000000 : ℚ) : ℝ) ≤ stT95 139 := by
  have hc : ((-161659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137117385551/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-161659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c140 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((86153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -761857/2500000) (δ := 3/390625) (ψ := -563897/1000000) 95 75
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t140 : ((72801988137/2500000000000 : ℚ) : ℝ) ≤ stT95 140 := by
  have hc : ((172281/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72801988137/2500000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((172281/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c141 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((42813/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1357029/10000000) (δ := 169/20000000) (ψ := -563897/1000000) 95 75
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t141 : ((72105810771/1000000000000 : ℚ) : ℝ) ≤ stT95 141 := by
  have hc : ((85621/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72105810771/1000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((85621/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c142 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((495873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321423/10000000) (δ := 21/4000000) (ψ := -563897/1000000) 95 75
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t142 : ((52013277561/625000000000 : ℚ) : ℝ) ≤ stT95 142 := by
  have hc : ((61981/62500 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52013277561/625000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((61981/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c143 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((350057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1988097/10000000) (δ := 167/25000000) (ψ := -563897/1000000) 95 75
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t143 : ((9147233117/156250000000 : ℚ) : ℝ) ≤ stT95 143 := by
  have hc : ((21877/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9147233117/156250000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((21877/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c144 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((11329/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910789/2500000) (δ := 189/20000000) (ψ := -563897/1000000) 95 75
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t144 : ((2359165723/250000000000 : ℚ) : ℝ) ≤ stT95 144 := by
  have hc : ((2831/25000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2359165723/250000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((2831/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c145 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-129371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5286761/10000000) (δ := 279/50000000) (ψ := -563897/1000000) 95 75
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t145 : ((-42978869797/1000000000000 : ℚ) : ℝ) ≤ stT95 145 := by
  have hc : ((-258767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42978869797/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-258767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c146 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-465443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 691907/1000000) (δ := 187/25000000) (ψ := -563897/1000000) 95 75
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t146 : ((-48153013701/625000000000 : ℚ) : ℝ) ≤ stT95 146 := by
  have hc : ((-116367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48153013701/625000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-116367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c147 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-3008/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7167727/10000000) (δ := 403/50000000) (ψ := -563897/1000000) 95 76
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t147 : ((-79394821407/1000000000000 : ℚ) : ℝ) ≤ stT95 147 := by
  have hc : ((-96261/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79394821407/1000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-96261/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c148 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-121391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5557551/10000000) (δ := 87/12500000) (ψ := -563897/1000000) 95 76
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t148 : ((-19958202999/400000000000 : ℚ) : ℝ) ≤ stT95 148 := by
  have hc : ((-121401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19958202999/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-121401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c149 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-12491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3958219/10000000) (δ := 927/100000000) (ψ := -563897/1000000) 95 76
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t149 : ((-321062141/312500000000 : ℚ) : ℝ) ≤ stT95 149 := by
  have hc : ((-12541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321062141/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-12541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c150 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((145861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -148099/625000) (δ := 219/25000000) (ψ := -563897/1000000) 95 76
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t150 : ((14885589607/312500000000 : ℚ) : ℝ) ≤ stT95 150 := by
  have hc : ((291697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14885589607/312500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((291697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c151 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((950299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -158301/2000000) (δ := 617/100000000) (ψ := -563897/1000000) 95 76
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t151 : ((193325308303/2500000000000 : ℚ) : ℝ) ≤ stT95 151 := by
  have hc : ((950249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193325308303/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((950249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c152 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((14878/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 776157/10000000) (δ := 787/100000000) (ψ := -563897/1000000) 95 76
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t152 : ((386144520597/5000000000000 : ℚ) : ℝ) ≤ stT95 152 := by
  have hc : ((476071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386144520597/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((476071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c153 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((148773/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116677/500000) (δ := 767/100000000) (ψ := -563897/1000000) 95 76
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t153 : ((60132861873/1250000000000 : ℚ) : ℝ) ≤ stT95 153 := by
  have hc : ((297521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60132861873/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((297521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c154 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((4621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3880777/10000000) (δ := 937/100000000) (ψ := -563897/1000000) 95 76
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t154 : ((3713630687/2500000000000 : ℚ) : ℝ) ≤ stT95 154 := by
  have hc : ((9217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3713630687/2500000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((9217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c155 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-56167/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5417999/10000000) (δ := 807/100000000) (ψ := -563897/1000000) 95 76
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t155 : ((-563980923/12500000000 : ℚ) : ℝ) ≤ stT95 155 := by
  have hc : ((-14043/25000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563980923/12500000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-14043/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c156 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-934673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1389067/2000000) (δ := 917/100000000) (ψ := -563897/1000000) 95 76
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t156 : ((-748377557443/10000000000000 : ℚ) : ℝ) ≤ stT95 156 := by
  have hc : ((-934723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-748377557443/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-934723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c157 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-970483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7245051/10000000) (δ := 463/50000000) (ψ := -563897/1000000) 95 77
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t157 : ((-774569770371/10000000000000 : ℚ) : ℝ) ≤ stT95 157 := by
  have hc : ((-970533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-774569770371/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-970533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c158 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-331211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5737109/10000000) (δ := 323/50000000) (ψ := -563897/1000000) 95 77
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t158 : ((-32939681211/625000000000 : ℚ) : ℝ) ≤ stT95 158 := by
  have hc : ((-82809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32939681211/625000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-82809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c159 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-62177/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2119341/5000000) (δ := 483/50000000) (ψ := -563897/1000000) 95 77
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t159 : ((-6166177563/625000000000 : ℚ) : ℝ) ≤ stT95 159 := by
  have hc : ((-31101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6166177563/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-31101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c160 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((453721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2749649/10000000) (δ := 423/50000000) (ψ := -563897/1000000) 95 77
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t160 : ((358658228799/10000000000000 : ℚ) : ℝ) ≤ stT95 160 := by
  have hc : ((453671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((358658228799/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((453671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c161 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((43687/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1269893/10000000) (δ := 597/100000000) (ψ := -563897/1000000) 95 77
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t161 : ((6885638259/100000000000 : ℚ) : ℝ) ≤ stT95 161 := by
  have hc : ((87369/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6885638259/100000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((87369/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c162 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((996779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2007/100000) (δ := 159/25000000) (ψ := -563897/1000000) 95 77
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t162 : ((391552030173/5000000000000 : ℚ) : ℝ) ≤ stT95 162 := by
  have hc : ((996729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391552030173/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((996729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c163 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((39349/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1662243/10000000) (δ := 483/50000000) (ψ := -563897/1000000) 95 77
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t163 : ((3081853959/50000000000 : ℚ) : ℝ) ≤ stT95 163 := by
  have hc : ((78693/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3081853959/50000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((78693/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c164 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((159587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3114847/10000000) (δ := 353/50000000) (ψ := -563897/1000000) 95 77
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t164 : ((15574607477/625000000000 : ℚ) : ℝ) ≤ stT95 164 := by
  have hc : ((79781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15574607477/625000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((79781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c165 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-62493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227931/500000) (δ := 667/100000000) (ψ := -563897/1000000) 95 77
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t165 : ((-97320938489/5000000000000 : ℚ) : ℝ) ≤ stT95 165 := by
  have hc : ((-125011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97320938489/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-125011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c166 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-735681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599367/1000000) (δ := 817/100000000) (ψ := -563897/1000000) 95 77
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t166 : ((-571038351381/10000000000000 : ℚ) : ℝ) ≤ stT95 166 := by
  have hc : ((-735731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-571038351381/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-735731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c167 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-492489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7420101/10000000) (δ := 423/50000000) (ψ := -563897/1000000) 95 77
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t167 : ((-2977493387/39062500000 : ℚ) : ℝ) ≤ stT95 167 := by
  have hc : ((-246257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2977493387/39062500000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-246257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c168 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-923529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1717487/2500000) (δ := 91/12500000) (ψ := -563897/1000000) 95 78
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t168 : ((-712556899343/10000000000000 : ℚ) : ℝ) ≤ stT95 168 := by
  have hc : ((-923579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-712556899343/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-923579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c169 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-575637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -170639/312500) (δ := 33/4000000) (ψ := -563897/1000000) 95 78
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t169 : ((-442836286697/10000000000000 : ℚ) : ℝ) ≤ stT95 169 := by
  have hc : ((-575687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-442836286697/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-575687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c170 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-10577/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31713/78125) (δ := 123/20000000) (ψ := -563897/1000000) 95 78
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t170 : ((-1623971691/400000000000 : ℚ) : ℝ) ≤ stT95 170 := by
  have hc : ((-10587/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1623971691/400000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-10587/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c171 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((19327/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1333149/5000000) (δ := 33/6250000) (ψ := -563897/1000000) 95 78
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t171 : ((591127787/16000000000 : ℚ) : ℝ) ≤ stT95 171 := by
  have hc : ((773/1600 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((591127787/16000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((773/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c172 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((871481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256291/2000000) (δ := 349/50000000) (ψ := -563897/1000000) 95 78
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t172 : ((166114791513/2500000000000 : ℚ) : ℝ) ≤ stT95 172 := by
  have hc : ((871431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166114791513/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((871431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c173 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((999273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95361/10000000) (δ := 111/12500000) (ψ := -563897/1000000) 95 78
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t173 : ((151938851711/2000000000000 : ℚ) : ℝ) ≤ stT95 173 := by
  have hc : ((999223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151938851711/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((999223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c174 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((833327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1464241/10000000) (δ := 469/50000000) (ψ := -563897/1000000) 95 78
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t174 : ((315852813573/5000000000000 : ℚ) : ℝ) ≤ stT95 174 := by
  have hc : ((833277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315852813573/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((833277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c175 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((1333/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 706319/2500000) (δ := 43/6250000) (ψ := -563897/1000000) 95 78
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t175 : ((4030135641/125000000000 : ℚ) : ℝ) ≤ stT95 175 := by
  have hc : ((42651/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4030135641/125000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((42651/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c176 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-12557/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1044639/2500000) (δ := 111/12500000) (ψ := -563897/1000000) 95 78
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t176 : ((-37879656087/5000000000000 : ℚ) : ℝ) ≤ stT95 176 := by
  have hc : ((-50253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37879656087/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-50253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c177 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-59629/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5524169/10000000) (δ := 129/20000000) (ψ := -563897/1000000) 95 78
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t177 : ((-22411858599/500000000000 : ℚ) : ℝ) ≤ stT95 177 := by
  have hc : ((-29817/50000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22411858599/500000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-29817/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c178 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-28823/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 34311/50000) (δ := 101/20000000) (ψ := -563897/1000000) 95 78
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t178 : ((-86419727919/1250000000000 : ℚ) : ℝ) ≤ stT95 178 := by
  have hc : ((-461193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86419727919/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-461193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c179 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-495417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7515227/10000000) (δ := 181/20000000) (ψ := -563897/1000000) 95 79
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t179 : ((-46288898339/625000000000 : ℚ) : ℝ) ≤ stT95 179 := by
  have hc : ((-247721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46288898339/625000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-247721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c180 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-78707/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -774013/1250000) (δ := 97/20000000) (ψ := -563897/1000000) 95 79
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t180 : ((-1833389421/31250000000 : ℚ) : ℝ) ≤ stT95 180 := by
  have hc : ((-9839/12500 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1833389421/31250000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-9839/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c181 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-92667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4876311/10000000) (δ := 133/20000000) (ψ := -563897/1000000) 95 79
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t181 : ((-27555283581/1000000000000 : ℚ) : ℝ) ≤ stT95 181 := by
  have hc : ((-185359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27555283581/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-185359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c182 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((28639/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -445971/1250000) (δ := 101/12500000) (ψ := -563897/1000000) 95 79
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t182 : ((21221217621/2000000000000 : ℚ) : ℝ) ≤ stT95 182 := by
  have hc : ((28629/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21221217621/2000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((28629/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c183 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((30823/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -453279/2000000) (δ := 239/50000000) (ψ := -563897/1000000) 95 79
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t183 : ((45566321661/1000000000000 : ℚ) : ℝ) ≤ stT95 183 := by
  have hc : ((61641/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45566321661/1000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((61641/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c184 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((925347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -486057/5000000) (δ := 259/50000000) (ψ := -563897/1000000) 95 79
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t184 : ((682137276073/10000000000000 : ℚ) : ℝ) ≤ stT95 184 := by
  have hc : ((925297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((682137276073/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((925297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c185 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((198413/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19697/625000) (δ := 149/20000000) (ψ := -563897/1000000) 95 79
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t185 : ((72934331621/1000000000000 : ℚ) : ℝ) ≤ stT95 185 := by
  have hc : ((198403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72934331621/1000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((198403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c186 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((401587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1595479/10000000) (δ := 43/6250000) (ψ := -563897/1000000) 95 79
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t186 : ((29443931307/500000000000 : ℚ) : ℝ) ≤ stT95 186 := by
  have hc : ((200781/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29443931307/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((200781/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c187 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((410699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143447/500000) (δ := 33/4000000) (ψ := -563897/1000000) 95 79
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t187 : ((37537014441/1250000000000 : ℚ) : ℝ) ≤ stT95 187 := by
  have hc : ((410649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37537014441/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((410649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c188 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-83351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 413561/1000000) (δ := 289/50000000) (ψ := -563897/1000000) 95 79
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t188 : ((-2433057373/400000000000 : ℚ) : ℝ) ≤ stT95 188 := by
  have hc : ((-83401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2433057373/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-83401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c189 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-277111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134889/250000) (δ := 33/4000000) (ψ := -563897/1000000) 95 79
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t189 : ((-12599174153/312500000000 : ℚ) : ℝ) ≤ stT95 189 := by
  have hc : ((-17321/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12599174153/312500000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-17321/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c190 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-886047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6648861/10000000) (δ := 167/25000000) (ψ := -563897/1000000) 95 79
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t190 : ((-642842993269/10000000000000 : ℚ) : ℝ) ≤ stT95 190 := by
  have hc : ((-886097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-642842993269/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-886097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c191 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-499931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -390619/500000) (δ := 347/50000000) (ψ := -563897/1000000) 95 80
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t191 : ((-3617556627/50000000000 : ℚ) : ℝ) ≤ stT95 191 := by
  have hc : ((-124989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3617556627/50000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-124989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c192 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-871411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6572169/10000000) (δ := 649/100000000) (ψ := -563897/1000000) 95 80
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t192 : ((-78615368271/1250000000000 : ℚ) : ℝ) ≤ stT95 192 := by
  have hc : ((-871461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78615368271/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-871461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c193 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-535047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6673/12500) (δ := 809/100000000) (ψ := -563897/1000000) 95 80
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t193 : ((-48146422769/1250000000000 : ℚ) : ℝ) ≤ stT95 193 := by
  have hc : ((-535097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48146422769/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-535097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c194 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-3677/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4111007/10000000) (δ := 529/100000000) (ψ := -563897/1000000) 95 80
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t194 : ((-5283460281/1000000000000 : ℚ) : ℝ) ≤ stT95 194 := by
  have hc : ((-7359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5283460281/1000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-7359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c195 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((403031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -722481/2500000) (δ := 549/100000000) (ψ := -563897/1000000) 95 80
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t195 : ((144290167917/5000000000000 : ℚ) : ℝ) ≤ stT95 195 := by
  have hc : ((402981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144290167917/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((402981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c196 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((3919/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -104693/625000) (δ := 539/100000000) (ψ := -563897/1000000) 95 80
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t196 : ((89571339/1600000000 : ℚ) : ℝ) ≤ stT95 196 := by
  have hc : ((627/800 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89571339/1600000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((627/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c197 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((491323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -233217/5000000) (δ := 11/1562500) (ψ := -563897/1000000) 95 80
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t197 : ((17501754303/250000000000 : ℚ) : ℝ) ≤ stT95 197 := by
  have hc : ((245649/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17501754303/250000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((245649/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c198 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((191393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7361/100000) (δ := 347/50000000) (ψ := -563897/1000000) 95 80
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t198 : ((136009965227/2000000000000 : ℚ) : ℝ) ≤ stT95 198 := by
  have hc : ((191383/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136009965227/2000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((191383/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c199 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((357899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60393/312500) (δ := 377/50000000) (ψ := -563897/1000000) 95 80
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t199 : ((126845039497/2500000000000 : ℚ) : ℝ) ≤ stT95 199 := by
  have hc : ((178937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126845039497/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((178937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c200 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((316061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 624611/2000000) (δ := 609/100000000) (ψ := -563897/1000000) 95 80
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t200 : ((111726637083/5000000000000 : ℚ) : ℝ) ≤ stT95 200 := by
  have hc : ((316011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111726637083/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((316011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c201 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-30331/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1076899/2500000) (δ := 113/12500000) (ψ := -563897/1000000) 95 80
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t201 : ((-10700451493/1000000000000 : ℚ) : ℝ) ≤ stT95 201 := by
  have hc : ((-30341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10700451493/1000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-30341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c202 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-36503/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5486259/10000000) (δ := 919/100000000) (ψ := -563897/1000000) 95 80
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t202 : ((-102742546151/2500000000000 : ℚ) : ℝ) ≤ stT95 202 := by
  have hc : ((-292049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102742546151/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-292049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c203 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-887939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6659101/10000000) (δ := 749/100000000) (ψ := -563897/1000000) 95 80
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t203 : ((-623246623507/10000000000000 : ℚ) : ℝ) ≤ stT95 203 := by
  have hc : ((-887989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-623246623507/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-887989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c204 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-499969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7826179/10000000) (δ := 869/100000000) (ψ := -563897/1000000) 95 80
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t204 : ((-175033149577/2500000000000 : ℚ) : ℝ) ≤ stT95 204 := by
  have hc : ((-249997/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175033149577/2500000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-249997/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c205 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-898951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6720413/10000000) (δ := 9/1250000) (ψ := -563897/1000000) 95 81
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t205 : ((-627890167431/10000000000000 : ℚ) : ℝ) ≤ stT95 205 := by
  have hc : ((-899001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-627890167431/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-899001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c206 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-609223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5564693/10000000) (δ := 31/5000000) (ψ := -563897/1000000) 95 81
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t206 : ((-212250607191/5000000000000 : ℚ) : ℝ) ≤ stT95 206 := by
  have hc : ((-609273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212250607191/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-609273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c207 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-193797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4414569/10000000) (δ := 11/1250000) (ψ := -563897/1000000) 95 81
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t207 : ((-134733163503/10000000000000 : ℚ) : ℝ) ≤ stT95 207 := by
  have hc : ((-193847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134733163503/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-193847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c208 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((129893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3269989/10000000) (δ := 73/10000000) (ψ := -563897/1000000) 95 81
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t208 : ((180094449/10000000000 : ℚ) : ℝ) ≤ stT95 208 := by
  have hc : ((32467/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180094449/10000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((32467/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c209 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((658209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1065449/5000000) (δ := 483/100000000) (ψ := -563897/1000000) 95 81
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t209 : ((227628897263/5000000000000 : ℚ) : ℝ) ≤ stT95 209 := by
  have hc : ((658159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227628897263/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((658159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c210 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((92149/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249311/2500000) (δ := 673/100000000) (ψ := -563897/1000000) 95 81
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t210 : ((794816867/12500000000 : ℚ) : ℝ) ≤ stT95 210 := by
  have hc : ((5759/6250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((794816867/12500000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((5759/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c211 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((998627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8189/625000) (δ := 653/100000000) (ψ := -563897/1000000) 95 81
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t211 : ((171862091739/2500000000000 : ℚ) : ℝ) ≤ stT95 211 := by
  have hc : ((998577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171862091739/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((998577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c212 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((438411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 626979/5000000) (δ := 71/10000000) (ψ := -563897/1000000) 95 81
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t212 : ((75271095393/1250000000000 : ℚ) : ℝ) ≤ stT95 212 := by
  have hc : ((219193/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75271095393/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((219193/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c213 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((582787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2371607/10000000) (δ := 31/5000000) (ψ := -563897/1000000) 95 81
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t213 : ((99821099889/2500000000000 : ℚ) : ℝ) ≤ stT95 213 := by
  have hc : ((582737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99821099889/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((582737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c214 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((88131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3484021/10000000) (δ := 823/100000000) (ψ := -563897/1000000) 95 81
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t214 : ((6022794001/500000000000 : ℚ) : ℝ) ≤ stT95 214 := by
  have hc : ((44053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6022794001/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((44053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c215 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-65647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4591249/10000000) (δ := 703/100000000) (ψ := -563897/1000000) 95 81
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t215 : ((-17911780281/1000000000000 : ℚ) : ℝ) ≤ stT95 215 := by
  have hc : ((-131319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17911780281/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-131319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c216 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-129841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5693339/10000000) (δ := 903/100000000) (ψ := -563897/1000000) 95 81
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t216 : ((-44176219157/1000000000000 : ℚ) : ℝ) ≤ stT95 216 := by
  have hc : ((-129851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44176219157/1000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-129851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c217 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-18217/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6790339/10000000) (δ := 1/200000) (ψ := -563897/1000000) 95 81
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t217 : ((-1236719821/20000000000 : ℚ) : ℝ) ≤ stT95 217 := by
  have hc : ((-9109/10000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1236719821/20000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-9109/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c218 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-15624/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7825669/10000000) (δ := 7/1250000) (ψ := -563897/1000000) 95 82
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t218 : ((-169319129499/2500000000000 : ℚ) : ℝ) ≤ stT95 218 := by
  have hc : ((-499993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169319129499/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-499993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c219 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-902133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -673871/1000000) (δ := 683/100000000) (ψ := -563897/1000000) 95 82
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t219 : ((-304819668027/5000000000000 : ℚ) : ℝ) ≤ stT95 219 := by
  have hc : ((-902183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304819668027/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-902183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c220 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-63799/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44193/78125) (δ := 543/100000000) (ψ := -563897/1000000) 95 82
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t220 : ((-53770821/1250000000 : ℚ) : ℝ) ≤ stT95 220 := by
  have hc : ((-15951/25000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53770821/1250000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-15951/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c221 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-258091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1144901/2500000) (δ := 943/100000000) (ψ := -563897/1000000) 95 82
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t221 : ((-173644480893/10000000000000 : ℚ) : ℝ) ≤ stT95 221 := by
  have hc : ((-258141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173644480893/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-258141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c222 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((83531/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -438421/1250000) (δ := 3/400000) (ψ := -563897/1000000) 95 82
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t222 : ((7005694117/625000000000 : ℚ) : ℝ) ≤ stT95 222 := by
  have hc : ((41753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7005694117/625000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((41753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c223 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((560357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48799/200000) (δ := 67/10000000) (ψ := -563897/1000000) 95 82
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t223 : ((375209022243/10000000000000 : ℚ) : ℝ) ≤ stT95 223 := by
  have hc : ((560307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375209022243/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((560307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c224 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((852041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1377309/10000000) (δ := 493/100000000) (ψ := -563897/1000000) 95 82
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t224 : ((569260342623/10000000000000 : ℚ) : ℝ) ≤ stT95 224 := by
  have hc : ((851991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569260342623/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((851991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c225 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((19837/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1597/50000) (δ := 933/100000000) (ψ := -563897/1000000) 95 82
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t225 : ((1652998347/25000000000 : ℚ) : ℝ) ≤ stT95 225 := by
  have hc : ((4959/5000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1652998347/25000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((4959/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c226 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((95723/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91727/1250000) (δ := 993/100000000) (ψ := -563897/1000000) 95 82
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t226 : ((3183532821/50000000000 : ℚ) : ℝ) ≤ stT95 226 := by
  have hc : ((47859/50000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3183532821/50000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((47859/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c227 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((378217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1782383/10000000) (δ := 813/100000000) (ψ := -563897/1000000) 95 82
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t227 : ((15688420551/312500000000 : ℚ) : ℝ) ≤ stT95 227 := by
  have hc : ((23637/31250 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15688420551/312500000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((23637/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c228 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((17047/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2826341/10000000) (δ := 693/100000000) (ψ := -563897/1000000) 95 82
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t228 : ((1128832397/40000000000 : ℚ) : ℝ) ≤ stT95 228 := by
  have hc : ((3409/8000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1128832397/40000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((3409/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c229 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((12251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 386573/1000000) (δ := 933/100000000) (ψ := -563897/1000000) 95 82
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t229 : ((2019790217/1250000000000 : ℚ) : ℝ) ≤ stT95 229 := by
  have hc : ((6113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2019790217/1250000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((6113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c230 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-37967/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490059/1000000) (δ := 883/100000000) (ψ := -563897/1000000) 95 82
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t230 : ((-6259503833/250000000000 : ℚ) : ℝ) ≤ stT95 230 := by
  have hc : ((-9493/25000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6259503833/250000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-9493/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c231 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-718461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 74137/125000) (δ := 883/100000000) (ψ := -563897/1000000) 95 82
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t231 : ((-14773304671/312500000000 : ℚ) : ℝ) ≤ stT95 231 := by
  have hc : ((-718511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14773304671/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-718511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c232 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-187261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86961/125000) (δ := 67/10000000) (ψ := -563897/1000000) 95 82
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t232 : ((-122949591443/2000000000000 : ℚ) : ℝ) ≤ stT95 232 := by
  have hc : ((-187271/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122949591443/2000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-187271/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c233 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-499381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7729577/10000000) (δ := 241/50000000) (ψ := -563897/1000000) 95 83
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t233 : ((-81792964383/1250000000000 : ℚ) : ℝ) ≤ stT95 233 := by
  have hc : ((-249703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81792964383/1250000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-249703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c234 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-17951/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1678111/2500000) (δ := 203/25000000) (ψ := -563897/1000000) 95 83
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t234 : ((-366737481/6250000000 : ℚ) : ℝ) ≤ stT95 234 := by
  have hc : ((-561/625 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366737481/6250000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-561/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c235 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-651123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113993/200000) (δ := 213/25000000) (ψ := -563897/1000000) 95 83
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t235 : ((-424779031917/10000000000000 : ℚ) : ℝ) ≤ stT95 235 := by
  have hc : ((-651173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-424779031917/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-651173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c236 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-4702/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1172789/2500000) (δ := 471/50000000) (ψ := -563897/1000000) 95 83
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t236 : ((-19592012421/1000000000000 : ℚ) : ℝ) ≤ stT95 236 := by
  have hc : ((-150489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19592012421/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-150489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c237 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((47939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1843463/5000000) (δ := 37/6250000) (ψ := -563897/1000000) 95 83
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t237 : ((15561724533/2500000000000 : ℚ) : ℝ) ≤ stT95 237 := by
  have hc : ((23957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15561724533/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((23957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c238 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((95187/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -671731/2500000) (δ := 691/100000000) (ψ := -563897/1000000) 95 83
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t238 : ((61694016931/2000000000000 : ℚ) : ℝ) ≤ stT95 238 := by
  have hc : ((95177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61694016931/2000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((95177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c239 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((389901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -422779/2500000) (δ := 123/25000000) (ψ := -563897/1000000) 95 83
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t239 : ((31523716387/625000000000 : ℚ) : ℝ) ≤ stT95 239 := by
  have hc : ((97469/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31523716387/625000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((97469/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c240 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((192223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139893/2000000) (δ := 47/6250000) (ψ := -563897/1000000) 95 83
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t240 : ((124072914861/2000000000000 : ℚ) : ℝ) ≤ stT95 240 := by
  have hc : ((192213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124072914861/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((192213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c241 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((993369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144031/5000000) (δ := 21/3125000) (ψ := -563897/1000000) 95 83
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t241 : ((159963098441/2500000000000 : ℚ) : ℝ) ≤ stT95 241 := by
  have hc : ((993319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159963098441/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((993319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c242 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((873427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271501/10000000) (δ := 89/12500000) (ψ := -563897/1000000) 95 83
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t242 : ((70178462081/1250000000000 : ℚ) : ℝ) ≤ stT95 242 := by
  have hc : ((873377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70178462081/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((873377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c243 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((621333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 562721/2500000) (δ := 271/50000000) (ψ := -563897/1000000) 95 83
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t243 : ((797106089/20000000000 : ℚ) : ℝ) ≤ stT95 243 := by
  have hc : ((621283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((797106089/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((621283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c244 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((276643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 806561/2500000) (δ := 371/50000000) (ψ := -563897/1000000) 95 83
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t244 : ((22133801639/1250000000000 : ℚ) : ℝ) ≤ stT95 244 := by
  have hc : ((276593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22133801639/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((276593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c245 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-108039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 262351/625000) (δ := 1041/100000000) (ψ := -563897/1000000) 95 83
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t245 : ((-69055576053/10000000000000 : ℚ) : ℝ) ≤ stT95 245 := by
  have hc : ((-108089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69055576053/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-108089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c246 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-237611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5165031/10000000) (δ := 153/25000000) (ψ := -563897/1000000) 95 83
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t246 : ((-37877811993/1250000000000 : ℚ) : ℝ) ≤ stT95 246 := by
  have hc : ((-59409/125000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37877811993/1250000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-59409/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c247 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-771129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6128521/10000000) (δ := 153/25000000) (ψ := -563897/1000000) 95 83
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t247 : ((-98137926003/2000000000000 : ℚ) : ℝ) ≤ stT95 247 := by
  have hc : ((-771179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98137926003/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-771179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c248 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-476721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3544059/5000000) (δ := 133/25000000) (ψ := -563897/1000000) 95 83
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t248 : ((-151367093373/2500000000000 : ℚ) : ℝ) ≤ stT95 248 := by
  have hc : ((-238373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151367093373/2500000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-238373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c249 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-997117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -766411/1000000) (δ := 441/50000000) (ψ := -563897/1000000) 95 84
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t249 : ((-25277186283/400000000000 : ℚ) : ℝ) ≤ stT95 249 := by
  have hc : ((-997167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25277186283/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-997167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_c250 :
    |Real.cos (((95 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-224377/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1342441/2000000) (δ := 821/100000000) (ψ := -563897/1000000) 95 84
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st95_t250 : ((-35479121403/625000000000 : ℚ) : ℝ) ≤ stT95 250 := by
  have hc : ((-448779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((95 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st95_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35479121403/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-448779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st95_p1 : ((845129/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT95 (i+1) := by
  rw [Finset.sum_range_one]
  exact st95_t1

theorem st95_p2 : ((512917351019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT95 (i+1))
      = (∑ i ∈ Finset.range 1, stT95 (i+1)) + stT95 2 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 1
    simpa using h
  have hprev := st95_p1
  have hstep := st95_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p3 : ((56606363113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT95 (i+1))
      = (∑ i ∈ Finset.range 2, stT95 (i+1)) + stT95 3 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 2
    simpa using h
  have hprev := st95_p2
  have hstep := st95_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p4 : ((1007362363113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT95 (i+1))
      = (∑ i ∈ Finset.range 3, stT95 (i+1)) + stT95 4 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 3
    simpa using h
  have hprev := st95_p3
  have hstep := st95_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p5 : ((1064759007357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT95 (i+1))
      = (∑ i ∈ Finset.range 4, stT95 (i+1)) + stT95 5 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 4
    simpa using h
  have hprev := st95_p4
  have hstep := st95_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p6 : ((2787741958083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT95 (i+1))
      = (∑ i ∈ Finset.range 5, stT95 (i+1)) + stT95 6 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 5
    simpa using h
  have hprev := st95_p5
  have hstep := st95_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p7 : ((-7675509909/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT95 (i+1))
      = (∑ i ∈ Finset.range 6, stT95 (i+1)) + stT95 7 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 6
    simpa using h
  have hprev := st95_p6
  have hstep := st95_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p8 : ((-1113552790981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT95 (i+1))
      = (∑ i ∈ Finset.range 7, stT95 (i+1)) + stT95 8 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 7
    simpa using h
  have hprev := st95_p7
  have hstep := st95_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p9 : ((-570414141391/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT95 (i+1))
      = (∑ i ∈ Finset.range 8, stT95 (i+1)) + stT95 9 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 8
    simpa using h
  have hprev := st95_p8
  have hstep := st95_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p10 : ((-1548972249903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT95 (i+1))
      = (∑ i ∈ Finset.range 9, stT95 (i+1)) + stT95 10 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 9
    simpa using h
  have hprev := st95_p9
  have hstep := st95_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p11 : ((-2398387150869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT95 (i+1))
      = (∑ i ∈ Finset.range 10, stT95 (i+1)) + stT95 11 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 10
    simpa using h
  have hprev := st95_p10
  have hstep := st95_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p12 : ((-3165426024789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT95 (i+1))
      = (∑ i ∈ Finset.range 11, stT95 (i+1)) + stT95 12 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 11
    simpa using h
  have hprev := st95_p11
  have hstep := st95_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p13 : ((-2209475459289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT95 (i+1))
      = (∑ i ∈ Finset.range 12, stT95 (i+1)) + stT95 13 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 12
    simpa using h
  have hprev := st95_p12
  have hstep := st95_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p14 : ((-875117793437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT95 (i+1))
      = (∑ i ∈ Finset.range 13, stT95 (i+1)) + stT95 14 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 13
    simpa using h
  have hprev := st95_p13
  have hstep := st95_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p15 : ((385237045961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT95 (i+1))
      = (∑ i ∈ Finset.range 14, stT95 (i+1)) + stT95 15 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 14
    simpa using h
  have hprev := st95_p14
  have hstep := st95_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p16 : ((1632449545961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT95 (i+1))
      = (∑ i ∈ Finset.range 15, stT95 (i+1)) + stT95 16 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 15
    simpa using h
  have hprev := st95_p15
  have hstep := st95_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p17 : ((2720191395011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT95 (i+1))
      = (∑ i ∈ Finset.range 16, stT95 (i+1)) + stT95 17 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 16
    simpa using h
  have hprev := st95_p16
  have hstep := st95_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p18 : ((3022941442823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT95 (i+1))
      = (∑ i ∈ Finset.range 17, stT95 (i+1)) + stT95 18 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 17
    simpa using h
  have hprev := st95_p17
  have hstep := st95_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p19 : ((2133732684497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT95 (i+1))
      = (∑ i ∈ Finset.range 18, stT95 (i+1)) + stT95 19 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 18
    simpa using h
  have hprev := st95_p18
  have hstep := st95_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p20 : ((1297918416947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT95 (i+1))
      = (∑ i ∈ Finset.range 19, stT95 (i+1)) + stT95 20 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 19
    simpa using h
  have hprev := st95_p19
  have hstep := st95_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p21 : ((1041720152437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT95 (i+1))
      = (∑ i ∈ Finset.range 20, stT95 (i+1)) + stT95 21 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 20
    simpa using h
  have hprev := st95_p20
  have hstep := st95_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p22 : ((2569979226323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT95 (i+1))
      = (∑ i ∈ Finset.range 21, stT95 (i+1)) + stT95 22 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 21
    simpa using h
  have hprev := st95_p21
  have hstep := st95_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p23 : ((3054957327651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT95 (i+1))
      = (∑ i ∈ Finset.range 22, stT95 (i+1)) + stT95 23 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 22
    simpa using h
  have hprev := st95_p22
  have hstep := st95_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p24 : ((2172893552513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT95 (i+1))
      = (∑ i ∈ Finset.range 23, stT95 (i+1)) + stT95 24 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 23
    simpa using h
  have hprev := st95_p23
  have hstep := st95_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p25 : ((2224636552513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT95 (i+1))
      = (∑ i ∈ Finset.range 24, stT95 (i+1)) + stT95 25 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 24
    simpa using h
  have hprev := st95_p24
  have hstep := st95_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p26 : ((1641989050447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT95 (i+1))
      = (∑ i ∈ Finset.range 25, stT95 (i+1)) + stT95 26 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 25
    simpa using h
  have hprev := st95_p25
  have hstep := st95_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p27 : ((2490573269197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT95 (i+1))
      = (∑ i ∈ Finset.range 26, stT95 (i+1)) + stT95 27 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 26
    simpa using h
  have hprev := st95_p26
  have hstep := st95_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p28 : ((1560466642579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT95 (i+1))
      = (∑ i ∈ Finset.range 27, stT95 (i+1)) + stT95 28 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 27
    simpa using h
  have hprev := st95_p27
  have hstep := st95_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p29 : ((497759660049/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT95 (i+1))
      = (∑ i ∈ Finset.range 28, stT95 (i+1)) + stT95 29 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 28
    simpa using h
  have hprev := st95_p28
  have hstep := st95_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p30 : ((1579878205933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT95 (i+1))
      = (∑ i ∈ Finset.range 29, stT95 (i+1)) + stT95 30 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 29
    simpa using h
  have hprev := st95_p29
  have hstep := st95_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p31 : ((1584538841/3200000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT95 (i+1))
      = (∑ i ∈ Finset.range 30, stT95 (i+1)) + stT95 31 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 30
    simpa using h
  have hprev := st95_p30
  have hstep := st95_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p32 : ((3186844300277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT95 (i+1))
      = (∑ i ∈ Finset.range 31, stT95 (i+1)) + stT95 32 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 31
    simpa using h
  have hprev := st95_p31
  have hstep := st95_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p33 : ((4861315883213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT95 (i+1))
      = (∑ i ∈ Finset.range 32, stT95 (i+1)) + stT95 33 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 32
    simpa using h
  have hprev := st95_p32
  have hstep := st95_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p34 : ((685768591393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT95 (i+1))
      = (∑ i ∈ Finset.range 33, stT95 (i+1)) + stT95 34 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 33
    simpa using h
  have hprev := st95_p33
  have hstep := st95_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p35 : ((4384227012569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT95 (i+1))
      = (∑ i ∈ Finset.range 34, stT95 (i+1)) + stT95 35 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 34
    simpa using h
  have hprev := st95_p34
  have hstep := st95_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p36 : ((4159176967559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT95 (i+1))
      = (∑ i ∈ Finset.range 35, stT95 (i+1)) + stT95 36 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 35
    simpa using h
  have hprev := st95_p35
  have hstep := st95_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p37 : ((3513905960589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT95 (i+1))
      = (∑ i ∈ Finset.range 36, stT95 (i+1)) + stT95 37 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 36
    simpa using h
  have hprev := st95_p36
  have hstep := st95_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p38 : ((977755873959/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT95 (i+1))
      = (∑ i ∈ Finset.range 37, stT95 (i+1)) + stT95 38 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 37
    simpa using h
  have hprev := st95_p37
  have hstep := st95_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p39 : ((3297908905359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT95 (i+1))
      = (∑ i ∈ Finset.range 38, stT95 (i+1)) + stT95 39 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 38
    simpa using h
  have hprev := st95_p38
  have hstep := st95_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p40 : ((34721965371/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT95 (i+1))
      = (∑ i ∈ Finset.range 39, stT95 (i+1)) + stT95 40 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 39
    simpa using h
  have hprev := st95_p39
  have hstep := st95_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p41 : ((2229318134067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT95 (i+1))
      = (∑ i ∈ Finset.range 40, stT95 (i+1)) + stT95 41 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 40
    simpa using h
  have hprev := st95_p40
  have hstep := st95_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p42 : ((64464862577/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT95 (i+1))
      = (∑ i ∈ Finset.range 41, stT95 (i+1)) + stT95 42 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 41
    simpa using h
  have hprev := st95_p41
  have hstep := st95_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p43 : ((234772724897/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT95 (i+1))
      = (∑ i ∈ Finset.range 42, stT95 (i+1)) + stT95 43 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 42
    simpa using h
  have hprev := st95_p42
  have hstep := st95_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p44 : ((1044768503461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT95 (i+1))
      = (∑ i ∈ Finset.range 43, stT95 (i+1)) + stT95 44 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 43
    simpa using h
  have hprev := st95_p43
  have hstep := st95_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p45 : ((817103985397/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT95 (i+1))
      = (∑ i ∈ Finset.range 44, stT95 (i+1)) + stT95 45 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 44
    simpa using h
  have hprev := st95_p44
  have hstep := st95_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p46 : ((4728351723751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT95 (i+1))
      = (∑ i ∈ Finset.range 45, stT95 (i+1)) + stT95 46 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 45
    simpa using h
  have hprev := st95_p45
  have hstep := st95_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p47 : ((4252337341401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT95 (i+1))
      = (∑ i ∈ Finset.range 46, stT95 (i+1)) + stT95 47 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 46
    simpa using h
  have hprev := st95_p46
  have hstep := st95_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p48 : ((3207698291529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT95 (i+1))
      = (∑ i ∈ Finset.range 47, stT95 (i+1)) + stT95 48 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 47
    simpa using h
  have hprev := st95_p47
  have hstep := st95_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p49 : ((2255696807353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT95 (i+1))
      = (∑ i ∈ Finset.range 48, stT95 (i+1)) + stT95 49 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 48
    simpa using h
  have hprev := st95_p48
  have hstep := st95_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p50 : ((922794145247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT95 (i+1))
      = (∑ i ∈ Finset.range 49, stT95 (i+1)) + stT95 50 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 49
    simpa using h
  have hprev := st95_p49
  have hstep := st95_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p51 : ((203314238773/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT95 (i+1))
      = (∑ i ∈ Finset.range 50, stT95 (i+1)) + stT95 51 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 50
    simpa using h
  have hprev := st95_p50
  have hstep := st95_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p52 : ((1966014578309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT95 (i+1))
      = (∑ i ∈ Finset.range 51, stT95 (i+1)) + stT95 52 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 51
    simpa using h
  have hprev := st95_p51
  have hstep := st95_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p53 : ((4936534130673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT95 (i+1))
      = (∑ i ∈ Finset.range 52, stT95 (i+1)) + stT95 53 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 52
    simpa using h
  have hprev := st95_p52
  have hstep := st95_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p54 : ((3825237078549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT95 (i+1))
      = (∑ i ∈ Finset.range 53, stT95 (i+1)) + stT95 54 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 53
    simpa using h
  have hprev := st95_p53
  have hstep := st95_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p55 : ((3247226540949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT95 (i+1))
      = (∑ i ∈ Finset.range 54, stT95 (i+1)) + stT95 55 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 54
    simpa using h
  have hprev := st95_p54
  have hstep := st95_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p56 : ((4522991197619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT95 (i+1))
      = (∑ i ∈ Finset.range 55, stT95 (i+1)) + stT95 56 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 55
    simpa using h
  have hprev := st95_p55
  have hstep := st95_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p57 : ((4774807247863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT95 (i+1))
      = (∑ i ∈ Finset.range 56, stT95 (i+1)) + stT95 57 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 56
    simpa using h
  have hprev := st95_p56
  have hstep := st95_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p58 : ((3469599628823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT95 (i+1))
      = (∑ i ∈ Finset.range 57, stT95 (i+1)) + stT95 58 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 57
    simpa using h
  have hprev := st95_p57
  have hstep := st95_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p59 : ((3395706956203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT95 (i+1))
      = (∑ i ∈ Finset.range 58, stT95 (i+1)) + stT95 59 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 58
    simpa using h
  have hprev := st95_p58
  have hstep := st95_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p60 : ((4686021893359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT95 (i+1))
      = (∑ i ∈ Finset.range 59, stT95 (i+1)) + stT95 60 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 59
    simpa using h
  have hprev := st95_p59
  have hstep := st95_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p61 : ((4726117897647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT95 (i+1))
      = (∑ i ∈ Finset.range 60, stT95 (i+1)) + stT95 61 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 60
    simpa using h
  have hprev := st95_p60
  have hstep := st95_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p62 : ((3458145360843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT95 (i+1))
      = (∑ i ∈ Finset.range 61, stT95 (i+1)) + stT95 62 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 61
    simpa using h
  have hprev := st95_p61
  have hstep := st95_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p63 : ((3322051647321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT95 (i+1))
      = (∑ i ∈ Finset.range 62, stT95 (i+1)) + stT95 63 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 62
    simpa using h
  have hprev := st95_p62
  have hstep := st95_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p64 : ((4551142897321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT95 (i+1))
      = (∑ i ∈ Finset.range 63, stT95 (i+1)) + stT95 64 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 63
    simpa using h
  have hprev := st95_p63
  have hstep := st95_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p65 : ((4894790956447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT95 (i+1))
      = (∑ i ∈ Finset.range 64, stT95 (i+1)) + stT95 65 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 64
    simpa using h
  have hprev := st95_p64
  have hstep := st95_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p66 : ((1880771453561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT95 (i+1))
      = (∑ i ∈ Finset.range 65, stT95 (i+1)) + stT95 66 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 65
    simpa using h
  have hprev := st95_p65
  have hstep := st95_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p67 : ((1564919315041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT95 (i+1))
      = (∑ i ∈ Finset.range 66, stT95 (i+1)) + stT95 67 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 66
    simpa using h
  have hprev := st95_p66
  have hstep := st95_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p68 : ((1013001568931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT95 (i+1))
      = (∑ i ∈ Finset.range 67, stT95 (i+1)) + stT95 68 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 67
    simpa using h
  have hprev := st95_p67
  have hstep := st95_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p69 : ((2493957790687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT95 (i+1))
      = (∑ i ∈ Finset.range 68, stT95 (i+1)) + stT95 69 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 68
    simpa using h
  have hprev := st95_p68
  have hstep := st95_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p70 : ((277491402943/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT95 (i+1))
      = (∑ i ∈ Finset.range 69, stT95 (i+1)) + stT95 70 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 69
    simpa using h
  have hprev := st95_p69
  have hstep := st95_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p71 : ((205675663777/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT95 (i+1))
      = (∑ i ∈ Finset.range 70, stT95 (i+1)) + stT95 71 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 70
    simpa using h
  have hprev := st95_p70
  have hstep := st95_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p72 : ((3303631641601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT95 (i+1))
      = (∑ i ∈ Finset.range 71, stT95 (i+1)) + stT95 72 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 71
    simpa using h
  have hprev := st95_p71
  have hstep := st95_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p73 : ((4437743514847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT95 (i+1))
      = (∑ i ∈ Finset.range 72, stT95 (i+1)) + stT95 73 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 72
    simpa using h
  have hprev := st95_p72
  have hstep := st95_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p74 : ((5023108304647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT95 (i+1))
      = (∑ i ∈ Finset.range 73, stT95 (i+1)) + stT95 74 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 73
    simpa using h
  have hprev := st95_p73
  have hstep := st95_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p75 : ((529767387593/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT95 (i+1))
      = (∑ i ∈ Finset.range 74, stT95 (i+1)) + stT95 75 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 74
    simpa using h
  have hprev := st95_p74
  have hstep := st95_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p76 : ((639558930923/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT95 (i+1))
      = (∑ i ∈ Finset.range 75, stT95 (i+1)) + stT95 76 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 75
    simpa using h
  have hprev := st95_p75
  have hstep := st95_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p77 : ((663657018253/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT95 (i+1))
      = (∑ i ∈ Finset.range 76, stT95 (i+1)) + stT95 77 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 76
    simpa using h
  have hprev := st95_p76
  have hstep := st95_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p78 : ((4418321635967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT95 (i+1))
      = (∑ i ∈ Finset.range 77, stT95 (i+1)) + stT95 78 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 77
    simpa using h
  have hprev := st95_p77
  have hstep := st95_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p79 : ((505315085063/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT95 (i+1))
      = (∑ i ∈ Finset.range 78, stT95 (i+1)) + stT95 79 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 78
    simpa using h
  have hprev := st95_p78
  have hstep := st95_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p80 : ((442605676037/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT95 (i+1))
      = (∑ i ∈ Finset.range 79, stT95 (i+1)) + stT95 80 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 79
    simpa using h
  have hprev := st95_p79
  have hstep := st95_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p81 : ((1669048500557/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT95 (i+1))
      = (∑ i ∈ Finset.range 80, stT95 (i+1)) + stT95 81 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 80
    simpa using h
  have hprev := st95_p80
  have hstep := st95_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p82 : ((1559110529809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT95 (i+1))
      = (∑ i ∈ Finset.range 81, stT95 (i+1)) + stT95 82 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 81
    simpa using h
  have hprev := st95_p81
  have hstep := st95_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p83 : ((1002932272167/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT95 (i+1))
      = (∑ i ∈ Finset.range 82, stT95 (i+1)) + stT95 83 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 82
    simpa using h
  have hprev := st95_p82
  have hstep := st95_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p84 : ((991916639603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT95 (i+1))
      = (∑ i ∈ Finset.range 83, stT95 (i+1)) + stT95 84 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 83
    simpa using h
  have hprev := st95_p83
  have hstep := st95_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p85 : ((1220495967109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT95 (i+1))
      = (∑ i ∈ Finset.range 84, stT95 (i+1)) + stT95 85 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 84
    simpa using h
  have hprev := st95_p84
  have hstep := st95_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p86 : ((970951188423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT95 (i+1))
      = (∑ i ∈ Finset.range 85, stT95 (i+1)) + stT95 86 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 85
    simpa using h
  have hprev := st95_p85
  have hstep := st95_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p87 : ((383851611111/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT95 (i+1))
      = (∑ i ∈ Finset.range 86, stT95 (i+1)) + stT95 87 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 86
    simpa using h
  have hprev := st95_p86
  have hstep := st95_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p88 : ((41358563279/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT95 (i+1))
      = (∑ i ∈ Finset.range 87, stT95 (i+1)) + stT95 88 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 87
    simpa using h
  have hprev := st95_p87
  have hstep := st95_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p89 : ((4329588312963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT95 (i+1))
      = (∑ i ∈ Finset.range 88, stT95 (i+1)) + stT95 89 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 88
    simpa using h
  have hprev := st95_p88
  have hstep := st95_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p90 : ((5072041175439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT95 (i+1))
      = (∑ i ∈ Finset.range 89, stT95 (i+1)) + stT95 90 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 89
    simpa using h
  have hprev := st95_p89
  have hstep := st95_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p91 : ((2397122301077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT95 (i+1))
      = (∑ i ∈ Finset.range 90, stT95 (i+1)) + stT95 91 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 90
    simpa using h
  have hprev := st95_p90
  have hstep := st95_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p92 : ((1893922357481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT95 (i+1))
      = (∑ i ∈ Finset.range 91, stT95 (i+1)) + stT95 92 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 91
    simpa using h
  have hprev := st95_p91
  have hstep := st95_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p93 : ((1519036211777/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT95 (i+1))
      = (∑ i ∈ Finset.range 92, stT95 (i+1)) + stT95 93 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 92
    simpa using h
  have hprev := st95_p92
  have hstep := st95_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p94 : ((81273066241/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT95 (i+1))
      = (∑ i ∈ Finset.range 93, stT95 (i+1)) + stT95 94 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 93
    simpa using h
  have hprev := st95_p93
  have hstep := st95_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p95 : ((84239022247/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT95 (i+1))
      = (∑ i ∈ Finset.range 94, stT95 (i+1)) + stT95 95 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 94
    simpa using h
  have hprev := st95_p94
  have hstep := st95_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p96 : ((503224483937/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT95 (i+1))
      = (∑ i ∈ Finset.range 95, stT95 (i+1)) + stT95 96 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 95
    simpa using h
  have hprev := st95_p95
  have hstep := st95_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p97 : ((199223156291/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT95 (i+1))
      = (∑ i ∈ Finset.range 96, stT95 (i+1)) + stT95 97 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 96
    simpa using h
  have hprev := st95_p96
  have hstep := st95_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p98 : ((2058509150241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT95 (i+1))
      = (∑ i ∈ Finset.range 97, stT95 (i+1)) + stT95 98 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 97
    simpa using h
  have hprev := st95_p97
  have hstep := st95_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p99 : ((799707664813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT95 (i+1))
      = (∑ i ∈ Finset.range 98, stT95 (i+1)) + stT95 99 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 98
    simpa using h
  have hprev := st95_p98
  have hstep := st95_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p100 : ((750735914813/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT95 (i+1))
      = (∑ i ∈ Finset.range 99, stT95 (i+1)) + stT95 100 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 99
    simpa using h
  have hprev := st95_p99
  have hstep := st95_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p101 : ((735963316693/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT95 (i+1))
      = (∑ i ∈ Finset.range 100, stT95 (i+1)) + stT95 101 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 100
    simpa using h
  have hprev := st95_p100
  have hstep := st95_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p102 : ((4663561292963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT95 (i+1))
      = (∑ i ∈ Finset.range 101, stT95 (i+1)) + stT95 102 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 101
    simpa using h
  have hprev := st95_p101
  have hstep := st95_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p103 : ((5162153532227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT95 (i+1))
      = (∑ i ∈ Finset.range 102, stT95 (i+1)) + stT95 103 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 102
    simpa using h
  have hprev := st95_p102
  have hstep := st95_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p104 : ((239589061223/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT95 (i+1))
      = (∑ i ∈ Finset.range 103, stT95 (i+1)) + stT95 104 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 103
    simpa using h
  have hprev := st95_p103
  have hstep := st95_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p105 : ((3852350620731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT95 (i+1))
      = (∑ i ∈ Finset.range 104, stT95 (i+1)) + stT95 105 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 104
    simpa using h
  have hprev := st95_p104
  have hstep := st95_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p106 : ((3065220446331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT95 (i+1))
      = (∑ i ∈ Finset.range 105, stT95 (i+1)) + stT95 106 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 105
    simpa using h
  have hprev := st95_p105
  have hstep := st95_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p107 : ((3014225069581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT95 (i+1))
      = (∑ i ∈ Finset.range 106, stT95 (i+1)) + stT95 107 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 106
    simpa using h
  have hprev := st95_p106
  have hstep := st95_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p108 : ((3724902505081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT95 (i+1))
      = (∑ i ∈ Finset.range 107, stT95 (i+1)) + stT95 108 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 107
    simpa using h
  have hprev := st95_p107
  have hstep := st95_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p109 : ((4673863825451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT95 (i+1))
      = (∑ i ∈ Finset.range 108, stT95 (i+1)) + stT95 109 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 108
    simpa using h
  have hprev := st95_p108
  have hstep := st95_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p110 : ((5186262885409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT95 (i+1))
      = (∑ i ∈ Finset.range 109, stT95 (i+1)) + stT95 110 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 109
    simpa using h
  have hprev := st95_p109
  have hstep := st95_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p111 : ((982539692993/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT95 (i+1))
      = (∑ i ∈ Finset.range 110, stT95 (i+1)) + stT95 111 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 110
    simpa using h
  have hprev := st95_p110
  have hstep := st95_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p112 : ((4052369317733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT95 (i+1))
      = (∑ i ∈ Finset.range 111, stT95 (i+1)) + stT95 112 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 111
    simpa using h
  have hprev := st95_p111
  have hstep := st95_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p113 : ((199536923421/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT95 (i+1))
      = (∑ i ∈ Finset.range 112, stT95 (i+1)) + stT95 113 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 112
    simpa using h
  have hprev := st95_p112
  have hstep := st95_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p114 : ((181354042817/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT95 (i+1))
      = (∑ i ∈ Finset.range 113, stT95 (i+1)) + stT95 114 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 113
    simpa using h
  have hprev := st95_p113
  have hstep := st95_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p115 : ((6562535891/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT95 (i+1))
      = (∑ i ∈ Finset.range 114, stT95 (i+1)) + stT95 115 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 114
    simpa using h
  have hprev := st95_p114
  have hstep := st95_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p116 : ((1065765622519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT95 (i+1))
      = (∑ i ∈ Finset.range 115, stT95 (i+1)) + stT95 116 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 115
    simpa using h
  have hprev := st95_p115
  have hstep := st95_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p117 : ((157368093893/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT95 (i+1))
      = (∑ i ∈ Finset.range 116, stT95 (i+1)) + stT95 117 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 116
    simpa using h
  have hprev := st95_p116
  have hstep := st95_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p118 : ((1300407864391/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT95 (i+1))
      = (∑ i ∈ Finset.range 117, stT95 (i+1)) + stT95 118 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 117
    simpa using h
  have hprev := st95_p117
  have hstep := st95_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p119 : ((583573207031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT95 (i+1))
      = (∑ i ∈ Finset.range 118, stT95 (i+1)) + stT95 119 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 118
    simpa using h
  have hprev := st95_p118
  have hstep := st95_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p120 : ((941664538449/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT95 (i+1))
      = (∑ i ∈ Finset.range 119, stT95 (i+1)) + stT95 120 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 119
    simpa using h
  have hprev := st95_p119
  have hstep := st95_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p121 : ((3033686262317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT95 (i+1))
      = (∑ i ∈ Finset.range 120, stT95 (i+1)) + stT95 121 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 120
    simpa using h
  have hprev := st95_p120
  have hstep := st95_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p122 : ((2893124906027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT95 (i+1))
      = (∑ i ∈ Finset.range 121, stT95 (i+1)) + stT95 122 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 121
    simpa using h
  have hprev := st95_p121
  have hstep := st95_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p123 : ((3416745734383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT95 (i+1))
      = (∑ i ∈ Finset.range 122, stT95 (i+1)) + stT95 123 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 122
    simpa using h
  have hprev := st95_p122
  have hstep := st95_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p124 : ((4299913894213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT95 (i+1))
      = (∑ i ∈ Finset.range 123, stT95 (i+1)) + stT95 124 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 123
    simpa using h
  have hprev := st95_p123
  have hstep := st95_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p125 : ((5047447359149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT95 (i+1))
      = (∑ i ∈ Finset.range 124, stT95 (i+1)) + stT95 125 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 124
    simpa using h
  have hprev := st95_p124
  have hstep := st95_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p126 : ((5252795566759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT95 (i+1))
      = (∑ i ∈ Finset.range 125, stT95 (i+1)) + stT95 126 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 125
    simpa using h
  have hprev := st95_p125
  have hstep := st95_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p127 : ((4813115497401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT95 (i+1))
      = (∑ i ∈ Finset.range 126, stT95 (i+1)) + stT95 127 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 126
    simpa using h
  have hprev := st95_p126
  have hstep := st95_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p128 : ((158824279653/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT95 (i+1))
      = (∑ i ∈ Finset.range 127, stT95 (i+1)) + stT95 128 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 127
    simpa using h
  have hprev := st95_p127
  have hstep := st95_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p129 : ((396372784197/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT95 (i+1))
      = (∑ i ∈ Finset.range 128, stT95 (i+1)) + stT95 129 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 128
    simpa using h
  have hprev := st95_p128
  have hstep := st95_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p130 : ((22071573579/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT95 (i+1))
      = (∑ i ∈ Finset.range 129, stT95 (i+1)) + stT95 130 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 129
    simpa using h
  have hprev := st95_p129
  have hstep := st95_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p131 : ((387776947203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT95 (i+1))
      = (∑ i ∈ Finset.range 130, stT95 (i+1)) + stT95 131 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 130
    simpa using h
  have hprev := st95_p130
  have hstep := st95_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p132 : ((481882862569/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT95 (i+1))
      = (∑ i ∈ Finset.range 131, stT95 (i+1)) + stT95 132 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 131
    simpa using h
  have hprev := st95_p131
  have hstep := st95_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p133 : ((2353151035817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT95 (i+1))
      = (∑ i ∈ Finset.range 132, stT95 (i+1)) + stT95 133 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 132
    simpa using h
  have hprev := st95_p132
  have hstep := st95_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p134 : ((2620619686307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT95 (i+1))
      = (∑ i ∈ Finset.range 133, stT95 (i+1)) + stT95 134 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 133
    simpa using h
  have hprev := st95_p133
  have hstep := st95_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p135 : ((2604038152949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT95 (i+1))
      = (∑ i ∈ Finset.range 134, stT95 (i+1)) + stT95 135 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 134
    simpa using h
  have hprev := st95_p134
  have hstep := st95_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p136 : ((2315044147103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT95 (i+1))
      = (∑ i ∈ Finset.range 135, stT95 (i+1)) + stT95 136 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 135
    simpa using h
  have hprev := st95_p135
  have hstep := st95_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p137 : ((378348615613/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT95 (i+1))
      = (∑ i ∈ Finset.range 136, stT95 (i+1)) + stT95 137 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 136
    simpa using h
  have hprev := st95_p136
  have hstep := st95_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p138 : ((47816720727/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT95 (i+1))
      = (∑ i ∈ Finset.range 137, stT95 (i+1)) + stT95 138 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 137
    simpa using h
  have hprev := st95_p137
  have hstep := st95_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p139 : ((1393017677713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT95 (i+1))
      = (∑ i ∈ Finset.range 138, stT95 (i+1)) + stT95 139 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 138
    simpa using h
  have hprev := st95_p138
  have hstep := st95_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p140 : ((1538621653987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT95 (i+1))
      = (∑ i ∈ Finset.range 139, stT95 (i+1)) + stT95 140 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 139
    simpa using h
  have hprev := st95_p139
  have hstep := st95_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p141 : ((949575353921/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT95 (i+1))
      = (∑ i ∈ Finset.range 140, stT95 (i+1)) + stT95 141 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 140
    simpa using h
  have hprev := st95_p140
  have hstep := st95_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p142 : ((231525692833/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT95 (i+1))
      = (∑ i ∈ Finset.range 141, stT95 (i+1)) + stT95 142 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 141
    simpa using h
  have hprev := st95_p141
  have hstep := st95_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p143 : ((1303984194037/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT95 (i+1))
      = (∑ i ∈ Finset.range 142, stT95 (i+1)) + stT95 143 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 142
    simpa using h
  have hprev := st95_p142
  have hstep := st95_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p144 : ((1327575851267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT95 (i+1))
      = (∑ i ∈ Finset.range 143, stT95 (i+1)) + stT95 144 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 143
    simpa using h
  have hprev := st95_p143
  have hstep := st95_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p145 : ((2440257353549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT95 (i+1))
      = (∑ i ∈ Finset.range 144, stT95 (i+1)) + stT95 145 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 144
    simpa using h
  have hprev := st95_p144
  have hstep := st95_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p146 : ((2055033243941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT95 (i+1))
      = (∑ i ∈ Finset.range 145, stT95 (i+1)) + stT95 146 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 145
    simpa using h
  have hprev := st95_p145
  have hstep := st95_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p147 : ((829029568453/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT95 (i+1))
      = (∑ i ∈ Finset.range 146, stT95 (i+1)) + stT95 147 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 146
    simpa using h
  have hprev := st95_p146
  have hstep := st95_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p148 : ((2817163198837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT95 (i+1))
      = (∑ i ∈ Finset.range 147, stT95 (i+1)) + stT95 148 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 147
    simpa using h
  have hprev := st95_p147
  have hstep := st95_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p149 : ((112275568413/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT95 (i+1))
      = (∑ i ∈ Finset.range 148, stT95 (i+1)) + stT95 149 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 148
    simpa using h
  have hprev := st95_p148
  have hstep := st95_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p150 : ((3283228077749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT95 (i+1))
      = (∑ i ∈ Finset.range 149, stT95 (i+1)) + stT95 150 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 149
    simpa using h
  have hprev := st95_p149
  have hstep := st95_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p151 : ((4056529310961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT95 (i+1))
      = (∑ i ∈ Finset.range 150, stT95 (i+1)) + stT95 151 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 150
    simpa using h
  have hprev := st95_p150
  have hstep := st95_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p152 : ((965763670431/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT95 (i+1))
      = (∑ i ∈ Finset.range 151, stT95 (i+1)) + stT95 152 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 151
    simpa using h
  have hprev := st95_p151
  have hstep := st95_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p153 : ((5309881247139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT95 (i+1))
      = (∑ i ∈ Finset.range 152, stT95 (i+1)) + stT95 153 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 152
    simpa using h
  have hprev := st95_p152
  have hstep := st95_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p154 : ((5324735769887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT95 (i+1))
      = (∑ i ∈ Finset.range 153, stT95 (i+1)) + stT95 154 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 153
    simpa using h
  have hprev := st95_p153
  have hstep := st95_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p155 : ((4873551031487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT95 (i+1))
      = (∑ i ∈ Finset.range 154, stT95 (i+1)) + stT95 155 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 154
    simpa using h
  have hprev := st95_p154
  have hstep := st95_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p156 : ((1031293368511/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT95 (i+1))
      = (∑ i ∈ Finset.range 155, stT95 (i+1)) + stT95 156 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 155
    simpa using h
  have hprev := st95_p155
  have hstep := st95_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p157 : ((3350603703673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT95 (i+1))
      = (∑ i ∈ Finset.range 156, stT95 (i+1)) + stT95 157 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 156
    simpa using h
  have hprev := st95_p156
  have hstep := st95_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p158 : ((2823568804297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT95 (i+1))
      = (∑ i ∈ Finset.range 157, stT95 (i+1)) + stT95 158 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 157
    simpa using h
  have hprev := st95_p157
  have hstep := st95_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p159 : ((2724909963289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT95 (i+1))
      = (∑ i ∈ Finset.range 158, stT95 (i+1)) + stT95 159 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 158
    simpa using h
  have hprev := st95_p158
  have hstep := st95_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p160 : ((385446024011/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT95 (i+1))
      = (∑ i ∈ Finset.range 159, stT95 (i+1)) + stT95 160 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 159
    simpa using h
  have hprev := st95_p159
  have hstep := st95_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p161 : ((943033004497/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT95 (i+1))
      = (∑ i ∈ Finset.range 160, stT95 (i+1)) + stT95 161 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 160
    simpa using h
  have hprev := st95_p160
  have hstep := st95_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p162 : ((2277618039167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT95 (i+1))
      = (∑ i ∈ Finset.range 161, stT95 (i+1)) + stT95 162 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 161
    simpa using h
  have hprev := st95_p161
  have hstep := st95_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p163 : ((2585803435067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT95 (i+1))
      = (∑ i ∈ Finset.range 162, stT95 (i+1)) + stT95 163 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 162
    simpa using h
  have hprev := st95_p162
  have hstep := st95_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p164 : ((2710400294883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT95 (i+1))
      = (∑ i ∈ Finset.range 163, stT95 (i+1)) + stT95 164 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 163
    simpa using h
  have hprev := st95_p163
  have hstep := st95_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p165 : ((1306539678197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT95 (i+1))
      = (∑ i ∈ Finset.range 164, stT95 (i+1)) + stT95 165 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 164
    simpa using h
  have hprev := st95_p164
  have hstep := st95_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p166 : ((4655120361407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT95 (i+1))
      = (∑ i ∈ Finset.range 165, stT95 (i+1)) + stT95 166 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 165
    simpa using h
  have hprev := st95_p165
  have hstep := st95_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p167 : ((778576410867/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT95 (i+1))
      = (∑ i ∈ Finset.range 166, stT95 (i+1)) + stT95 167 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 166
    simpa using h
  have hprev := st95_p166
  have hstep := st95_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p168 : ((198770322187/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT95 (i+1))
      = (∑ i ∈ Finset.range 167, stT95 (i+1)) + stT95 168 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 167
    simpa using h
  have hprev := st95_p167
  have hstep := st95_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p169 : ((547497773659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT95 (i+1))
      = (∑ i ∈ Finset.range 168, stT95 (i+1)) + stT95 169 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 168
    simpa using h
  have hprev := st95_p168
  have hstep := st95_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p170 : ((134844478801/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT95 (i+1))
      = (∑ i ∈ Finset.range 169, stT95 (i+1)) + stT95 170 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 169
    simpa using h
  have hprev := st95_p169
  have hstep := st95_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p171 : ((613268888579/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT95 (i+1))
      = (∑ i ∈ Finset.range 170, stT95 (i+1)) + stT95 171 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 170
    simpa using h
  have hprev := st95_p170
  have hstep := st95_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p172 : ((3730803608947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT95 (i+1))
      = (∑ i ∈ Finset.range 171, stT95 (i+1)) + stT95 172 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 171
    simpa using h
  have hprev := st95_p171
  have hstep := st95_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p173 : ((2245248933751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT95 (i+1))
      = (∑ i ∈ Finset.range 172, stT95 (i+1)) + stT95 173 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 172
    simpa using h
  have hprev := st95_p172
  have hstep := st95_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p174 : ((640275436831/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT95 (i+1))
      = (∑ i ∈ Finset.range 173, stT95 (i+1)) + stT95 174 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 173
    simpa using h
  have hprev := st95_p173
  have hstep := st95_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p175 : ((680576793241/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT95 (i+1))
      = (∑ i ∈ Finset.range 174, stT95 (i+1)) + stT95 175 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 174
    simpa using h
  have hprev := st95_p174
  have hstep := st95_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p176 : ((2684427516877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT95 (i+1))
      = (∑ i ∈ Finset.range 175, stT95 (i+1)) + stT95 176 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 175
    simpa using h
  have hprev := st95_p175
  have hstep := st95_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p177 : ((2460308930887/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT95 (i+1))
      = (∑ i ∈ Finset.range 176, stT95 (i+1)) + stT95 177 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 176
    simpa using h
  have hprev := st95_p176
  have hstep := st95_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p178 : ((2114630019211/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT95 (i+1))
      = (∑ i ∈ Finset.range 177, stT95 (i+1)) + stT95 178 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 177
    simpa using h
  have hprev := st95_p177
  have hstep := st95_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p179 : ((1744318832499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT95 (i+1))
      = (∑ i ∈ Finset.range 178, stT95 (i+1)) + stT95 179 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 178
    simpa using h
  have hprev := st95_p178
  have hstep := st95_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p180 : ((1450976525139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT95 (i+1))
      = (∑ i ∈ Finset.range 179, stT95 (i+1)) + stT95 180 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 179
    simpa using h
  have hprev := st95_p179
  have hstep := st95_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p181 : ((656600053617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT95 (i+1))
      = (∑ i ∈ Finset.range 180, stT95 (i+1)) + stT95 181 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 180
    simpa using h
  have hprev := st95_p180
  have hstep := st95_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p182 : ((2732506302573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT95 (i+1))
      = (∑ i ∈ Finset.range 181, stT95 (i+1)) + stT95 182 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 181
    simpa using h
  have hprev := st95_p181
  have hstep := st95_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p183 : ((3188169519183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT95 (i+1))
      = (∑ i ∈ Finset.range 182, stT95 (i+1)) + stT95 183 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 182
    simpa using h
  have hprev := st95_p182
  have hstep := st95_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p184 : ((483788349407/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT95 (i+1))
      = (∑ i ∈ Finset.range 183, stT95 (i+1)) + stT95 184 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 183
    simpa using h
  have hprev := st95_p183
  have hstep := st95_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p185 : ((2299825055733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT95 (i+1))
      = (∑ i ∈ Finset.range 184, stT95 (i+1)) + stT95 185 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 184
    simpa using h
  have hprev := st95_p184
  have hstep := st95_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p186 : ((2594264368803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT95 (i+1))
      = (∑ i ∈ Finset.range 185, stT95 (i+1)) + stT95 186 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 185
    simpa using h
  have hprev := st95_p185
  have hstep := st95_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p187 : ((2744412426567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT95 (i+1))
      = (∑ i ∈ Finset.range 186, stT95 (i+1)) + stT95 187 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 186
    simpa using h
  have hprev := st95_p186
  have hstep := st95_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p188 : ((5427998418809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT95 (i+1))
      = (∑ i ∈ Finset.range 187, stT95 (i+1)) + stT95 188 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 187
    simpa using h
  have hprev := st95_p187
  have hstep := st95_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p189 : ((5024824845913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT95 (i+1))
      = (∑ i ∈ Finset.range 188, stT95 (i+1)) + stT95 189 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 188
    simpa using h
  have hprev := st95_p188
  have hstep := st95_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p190 : ((1095495463161/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT95 (i+1))
      = (∑ i ∈ Finset.range 189, stT95 (i+1)) + stT95 190 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 189
    simpa using h
  have hprev := st95_p189
  have hstep := st95_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p191 : ((914617631811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT95 (i+1))
      = (∑ i ∈ Finset.range 190, stT95 (i+1)) + stT95 191 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 190
    simpa using h
  have hprev := st95_p190
  have hstep := st95_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p192 : ((757386895269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT95 (i+1))
      = (∑ i ∈ Finset.range 191, stT95 (i+1)) + stT95 192 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 191
    simpa using h
  have hprev := st95_p191
  have hstep := st95_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p193 : ((661094049731/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT95 (i+1))
      = (∑ i ∈ Finset.range 192, stT95 (i+1)) + stT95 193 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 192
    simpa using h
  have hprev := st95_p192
  have hstep := st95_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p194 : ((1295770798057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT95 (i+1))
      = (∑ i ∈ Finset.range 193, stT95 (i+1)) + stT95 194 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 193
    simpa using h
  have hprev := st95_p193
  have hstep := st95_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p195 : ((720030482987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT95 (i+1))
      = (∑ i ∈ Finset.range 194, stT95 (i+1)) + stT95 195 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 194
    simpa using h
  have hprev := st95_p194
  have hstep := st95_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p196 : ((1719971400349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT95 (i+1))
      = (∑ i ∈ Finset.range 195, stT95 (i+1)) + stT95 196 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 195
    simpa using h
  have hprev := st95_p195
  have hstep := st95_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p197 : ((2070006486409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT95 (i+1))
      = (∑ i ∈ Finset.range 196, stT95 (i+1)) + stT95 197 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 196
    simpa using h
  have hprev := st95_p196
  have hstep := st95_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p198 : ((4820062798953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT95 (i+1))
      = (∑ i ∈ Finset.range 197, stT95 (i+1)) + stT95 198 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 197
    simpa using h
  have hprev := st95_p197
  have hstep := st95_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p199 : ((5327442956941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT95 (i+1))
      = (∑ i ∈ Finset.range 198, stT95 (i+1)) + stT95 199 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 198
    simpa using h
  have hprev := st95_p198
  have hstep := st95_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p200 : ((5550896231107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT95 (i+1))
      = (∑ i ∈ Finset.range 199, stT95 (i+1)) + stT95 200 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 199
    simpa using h
  have hprev := st95_p199
  have hstep := st95_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p201 : ((5443891716177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT95 (i+1))
      = (∑ i ∈ Finset.range 200, stT95 (i+1)) + stT95 201 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 200
    simpa using h
  have hprev := st95_p200
  have hstep := st95_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p202 : ((5032921531573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT95 (i+1))
      = (∑ i ∈ Finset.range 201, stT95 (i+1)) + stT95 202 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 201
    simpa using h
  have hprev := st95_p201
  have hstep := st95_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p203 : ((2204837454033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT95 (i+1))
      = (∑ i ∈ Finset.range 202, stT95 (i+1)) + stT95 203 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 202
    simpa using h
  have hprev := st95_p202
  have hstep := st95_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p204 : ((1854771154879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT95 (i+1))
      = (∑ i ∈ Finset.range 203, stT95 (i+1)) + stT95 204 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 203
    simpa using h
  have hprev := st95_p203
  have hstep := st95_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p205 : ((3081652142327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT95 (i+1))
      = (∑ i ∈ Finset.range 204, stT95 (i+1)) + stT95 205 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 204
    simpa using h
  have hprev := st95_p204
  have hstep := st95_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p206 : ((531430185589/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT95 (i+1))
      = (∑ i ∈ Finset.range 205, stT95 (i+1)) + stT95 206 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 205
    simpa using h
  have hprev := st95_p205
  have hstep := st95_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p207 : ((1261208882221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT95 (i+1))
      = (∑ i ∈ Finset.range 206, stT95 (i+1)) + stT95 207 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 206
    simpa using h
  have hprev := st95_p206
  have hstep := st95_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p208 : ((1351256106721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT95 (i+1))
      = (∑ i ∈ Finset.range 207, stT95 (i+1)) + stT95 208 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 207
    simpa using h
  have hprev := st95_p207
  have hstep := st95_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p209 : ((98680312749/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT95 (i+1))
      = (∑ i ∈ Finset.range 208, stT95 (i+1)) + stT95 209 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 208
    simpa using h
  have hprev := st95_p208
  have hstep := st95_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p210 : ((14818841803/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT95 (i+1))
      = (∑ i ∈ Finset.range 209, stT95 (i+1)) + stT95 210 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 209
    simpa using h
  have hprev := st95_p209
  have hstep := st95_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p211 : ((1120267967131/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT95 (i+1))
      = (∑ i ∈ Finset.range 210, stT95 (i+1)) + stT95 211 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 210
    simpa using h
  have hprev := st95_p210
  have hstep := st95_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p212 : ((1270810157917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT95 (i+1))
      = (∑ i ∈ Finset.range 211, stT95 (i+1)) + stT95 212 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 211
    simpa using h
  have hprev := st95_p211
  have hstep := st95_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p213 : ((685315628903/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT95 (i+1))
      = (∑ i ∈ Finset.range 212, stT95 (i+1)) + stT95 213 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 212
    simpa using h
  have hprev := st95_p212
  have hstep := st95_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p214 : ((1400745227811/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT95 (i+1))
      = (∑ i ∈ Finset.range 213, stT95 (i+1)) + stT95 214 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 213
    simpa using h
  have hprev := st95_p213
  have hstep := st95_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p215 : ((2711931554217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT95 (i+1))
      = (∑ i ∈ Finset.range 214, stT95 (i+1)) + stT95 215 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 214
    simpa using h
  have hprev := st95_p214
  have hstep := st95_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p216 : ((38922663413/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT95 (i+1))
      = (∑ i ∈ Finset.range 215, stT95 (i+1)) + stT95 216 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 215
    simpa using h
  have hprev := st95_p215
  have hstep := st95_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p217 : ((1090935251591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT95 (i+1))
      = (∑ i ∈ Finset.range 216, stT95 (i+1)) + stT95 217 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 216
    simpa using h
  have hprev := st95_p216
  have hstep := st95_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p218 : ((230404030523/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT95 (i+1))
      = (∑ i ∈ Finset.range 217, stT95 (i+1)) + stT95 218 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 217
    simpa using h
  have hprev := st95_p217
  have hstep := st95_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p219 : ((1538412576157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT95 (i+1))
      = (∑ i ∈ Finset.range 218, stT95 (i+1)) + stT95 219 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 218
    simpa using h
  have hprev := st95_p218
  have hstep := st95_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p220 : ((1323329292157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT95 (i+1))
      = (∑ i ∈ Finset.range 219, stT95 (i+1)) + stT95 220 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 219
    simpa using h
  have hprev := st95_p219
  have hstep := st95_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p221 : ((2473014103421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT95 (i+1))
      = (∑ i ∈ Finset.range 220, stT95 (i+1)) + stT95 221 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 220
    simpa using h
  have hprev := st95_p220
  have hstep := st95_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p222 : ((2585105209293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT95 (i+1))
      = (∑ i ∈ Finset.range 221, stT95 (i+1)) + stT95 222 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 221
    simpa using h
  have hprev := st95_p221
  have hstep := st95_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p223 : ((185019639471/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT95 (i+1))
      = (∑ i ∈ Finset.range 222, stT95 (i+1)) + stT95 223 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 222
    simpa using h
  have hprev := st95_p222
  have hstep := st95_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p224 : ((3529574574159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT95 (i+1))
      = (∑ i ∈ Finset.range 223, stT95 (i+1)) + stT95 224 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 223
    simpa using h
  have hprev := st95_p223
  have hstep := st95_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p225 : ((4190773912959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT95 (i+1))
      = (∑ i ∈ Finset.range 224, stT95 (i+1)) + stT95 225 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 224
    simpa using h
  have hprev := st95_p224
  have hstep := st95_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p226 : ((4827480477159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT95 (i+1))
      = (∑ i ∈ Finset.range 225, stT95 (i+1)) + stT95 226 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 225
    simpa using h
  have hprev := st95_p225
  have hstep := st95_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p227 : ((5329509934791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT95 (i+1))
      = (∑ i ∈ Finset.range 226, stT95 (i+1)) + stT95 227 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 226
    simpa using h
  have hprev := st95_p226
  have hstep := st95_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p228 : ((5611718034041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT95 (i+1))
      = (∑ i ∈ Finset.range 227, stT95 (i+1)) + stT95 228 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 227
    simpa using h
  have hprev := st95_p227
  have hstep := st95_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p229 : ((5627876355777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT95 (i+1))
      = (∑ i ∈ Finset.range 228, stT95 (i+1)) + stT95 229 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 228
    simpa using h
  have hprev := st95_p228
  have hstep := st95_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p230 : ((5377496202457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT95 (i+1))
      = (∑ i ∈ Finset.range 229, stT95 (i+1)) + stT95 230 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 229
    simpa using h
  have hprev := st95_p229
  have hstep := st95_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p231 : ((980950090597/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT95 (i+1))
      = (∑ i ∈ Finset.range 230, stT95 (i+1)) + stT95 231 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 230
    simpa using h
  have hprev := st95_p230
  have hstep := st95_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p232 : ((429000249577/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT95 (i+1))
      = (∑ i ∈ Finset.range 231, stT95 (i+1)) + stT95 232 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 231
    simpa using h
  have hprev := st95_p231
  have hstep := st95_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p233 : ((1817829390353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT95 (i+1))
      = (∑ i ∈ Finset.range 232, stT95 (i+1)) + stT95 233 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 232
    simpa using h
  have hprev := st95_p232
  have hstep := st95_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p234 : ((1524439405553/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT95 (i+1))
      = (∑ i ∈ Finset.range 233, stT95 (i+1)) + stT95 234 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 233
    simpa using h
  have hprev := st95_p233
  have hstep := st95_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p235 : ((2624099779189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT95 (i+1))
      = (∑ i ∈ Finset.range 234, stT95 (i+1)) + stT95 235 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 234
    simpa using h
  have hprev := st95_p234
  have hstep := st95_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p236 : ((2428179654979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT95 (i+1))
      = (∑ i ∈ Finset.range 235, stT95 (i+1)) + stT95 236 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 235
    simpa using h
  have hprev := st95_p235
  have hstep := st95_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p237 : ((2490426553111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT95 (i+1))
      = (∑ i ∈ Finset.range 236, stT95 (i+1)) + stT95 237 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 236
    simpa using h
  have hprev := st95_p236
  have hstep := st95_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p238 : ((1399448318883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT95 (i+1))
      = (∑ i ∈ Finset.range 237, stT95 (i+1)) + stT95 238 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 237
    simpa using h
  have hprev := st95_p237
  have hstep := st95_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p239 : ((1651638049979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT95 (i+1))
      = (∑ i ∈ Finset.range 238, stT95 (i+1)) + stT95 239 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 238
    simpa using h
  have hprev := st95_p238
  have hstep := st95_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p240 : ((3923640674263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT95 (i+1))
      = (∑ i ∈ Finset.range 239, stT95 (i+1)) + stT95 240 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 239
    simpa using h
  have hprev := st95_p239
  have hstep := st95_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p241 : ((4563493068027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT95 (i+1))
      = (∑ i ∈ Finset.range 240, stT95 (i+1)) + stT95 241 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 240
    simpa using h
  have hprev := st95_p240
  have hstep := st95_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p242 : ((204996830587/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT95 (i+1))
      = (∑ i ∈ Finset.range 241, stT95 (i+1)) + stT95 242 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 241
    simpa using h
  have hprev := st95_p241
  have hstep := st95_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p243 : ((220938952367/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT95 (i+1))
      = (∑ i ∈ Finset.range 242, stT95 (i+1)) + stT95 243 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 242
    simpa using h
  have hprev := st95_p242
  have hstep := st95_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p244 : ((5700544222287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT95 (i+1))
      = (∑ i ∈ Finset.range 243, stT95 (i+1)) + stT95 244 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 243
    simpa using h
  have hprev := st95_p243
  have hstep := st95_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p245 : ((2815744323117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT95 (i+1))
      = (∑ i ∈ Finset.range 244, stT95 (i+1)) + stT95 245 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 244
    simpa using h
  have hprev := st95_p244
  have hstep := st95_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p246 : ((532846615029/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT95 (i+1))
      = (∑ i ∈ Finset.range 245, stT95 (i+1)) + stT95 246 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 245
    simpa using h
  have hprev := st95_p245
  have hstep := st95_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p247 : ((193511060811/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT95 (i+1))
      = (∑ i ∈ Finset.range 246, stT95 (i+1)) + stT95 247 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 246
    simpa using h
  have hprev := st95_p246
  have hstep := st95_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p248 : ((4232308146783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT95 (i+1))
      = (∑ i ∈ Finset.range 247, stT95 (i+1)) + stT95 248 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 247
    simpa using h
  have hprev := st95_p247
  have hstep := st95_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p249 : ((900094622427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT95 (i+1))
      = (∑ i ∈ Finset.range 248, stT95 (i+1)) + stT95 249 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 248
    simpa using h
  have hprev := st95_p248
  have hstep := st95_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_p250 : ((151635627363/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT95 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT95 (i+1))
      = (∑ i ∈ Finset.range 249, stT95 (i+1)) + stT95 250 := by
    have h := Finset.sum_range_succ (fun i => stT95 (i+1)) 249
    simpa using h
  have hprev := st95_p249
  have hstep := st95_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st95_s250 :
    |Real.sin (((95 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-563897/1000000 : ℚ) : ℝ))
      - ((-220499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1342441/2000000) (δ := 821/100000000) (ψ := -563897/1000000) 95 84
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 95`** (evaluated boundary). -/
theorem station_95_sign : 0 < hardyG (((95:ℕ)):ℝ) := by
  have hcore := phase_station_lower_eval 95 250 (by norm_num) (by norm_num)
    ((-563897/1000000 : ℚ) : ℝ)
  have hchain := st95_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT95 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((95:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-563897/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st95_c250
  have hsinb := abs_le.mp st95_s250
  have hbdy_lo : ((5355475759399/72202000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos ((((95:ℕ)):ℝ) * Real.log ((250:ℕ)) - ((-563897/1000000 : ℚ) : ℝ))) / 2
          - (((95:ℕ)):ℝ)
            * Real.sin ((((95:ℕ)):ℝ) * Real.log ((250:ℕ)) - ((-563897/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + (((95:ℕ)):ℝ) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((95:ℝ) * Real.log ((250:ℝ)) - ((-563897/1000000 : ℚ) : ℝ))) / 2
        - (95:ℝ) * Real.sin ((95:ℝ) * Real.log ((250:ℝ)) - ((-563897/1000000 : ℚ) : ℝ))
        ≥ ((42338789/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + (95:ℝ) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((42338789/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((42338789/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((42338789/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((95:ℕ)):ℝ)+1) * ((((95:ℕ)):ℝ)+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((8949805799/39062500000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((151635627363/500000000000 : ℚ) : ℝ) + ((5355475759399/72202000000000 : ℚ) : ℝ)
      - ((8949805799/39062500000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-563897/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((95:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-563897/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((95:ℕ)):ℝ))).re
      - Real.sin ((-563897/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((95:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((95:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((95:ℕ)):ℝ)
      = ((((95:ℕ)):ℝ) * (Real.log (((95:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((95:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_95
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
  have hθwin : |(((-563897/1000000 : ℚ) : ℝ) + ((13:ℤ)) * (2*Real.pi)) - theta (((95:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((95:ℕ)):ℝ))
    (φ := ((-563897/1000000 : ℚ) : ℝ) + ((13:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-563897/1000000 : ℚ)) : ℝ) 13).1,
    (cos_sin_shift (((-563897/1000000 : ℚ)) : ℝ) 13).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_95_sign
end AxiomAudit
