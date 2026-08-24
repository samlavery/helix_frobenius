import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 168` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT168 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((168 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((14699/1000000 : ℚ) : ℝ))

theorem st168_c1 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((249973/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9187/2500000) (δ := 201/1000000000) (ψ := 14699/1000000) 168 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t1 : ((499921/500000 : ℚ) : ℝ) ≤ stT168 1 := by
  have hc : ((499921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499921/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((499921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c2 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-981029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7366247/10000000) (δ := 1713/200000000) (ψ := 14699/1000000) 168 19
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t2 : ((-1734319080593/2500000000000 : ℚ) : ℝ) ≤ stT168 2 := by
  have hc : ((-981079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1734319080593/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-981079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c3 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-695409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5849463/10000000) (δ := 851/100000000) (ψ := 14699/1000000) 168 29
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t3 : ((-4015234622877/10000000000000 : ℚ) : ℝ) ≤ stT168 3 := by
  have hc : ((-695459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4015234622877/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-695459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c4 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((114893/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1012239/10000000) (δ := 8567/1000000000) (ψ := 14699/1000000) 168 37
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t4 : ((459547/1000000 : ℚ) : ℝ) ≤ stT168 4 := by
  have hc : ((459547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((459547/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((459547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c5 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((981259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484771/10000000) (δ := 841/100000000) (ψ := 14699/1000000) 168 43
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t5 : ((877619822243/2000000000000 : ℚ) : ℝ) ≤ stT168 5 := by
  have hc : ((981209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((877619822243/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((981209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c6 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((829823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296003/2000000) (δ := 4273/500000000) (ψ := 14699/1000000) 168 48
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t6 : ((1693766668293/5000000000000 : ℚ) : ℝ) ≤ stT168 6 := by
  have hc : ((829773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1693766668293/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((829773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c7 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((985147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 215713/5000000) (δ := 343/40000000) (ψ := 14699/1000000) 168 52
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t7 : ((930828991367/2500000000000 : ℚ) : ℝ) ≤ stT168 7 := by
  have hc : ((985097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((930828991367/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((985097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c8 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-204237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157931/250000) (δ := 8599/1000000000) (ψ := 14699/1000000) 168 56
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t8 : ((-722131051733/2500000000000 : ℚ) : ℝ) ≤ stT168 8 := by
  have hc : ((-408499/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-722131051733/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-408499/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c9 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-1811/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3972269/10000000) (δ := 341/40000000) (ψ := 14699/1000000) 168 59
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t9 : ((-378333409/62500000000 : ℚ) : ℝ) ≤ stT168 9 := by
  have hc : ((-227/12500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378333409/62500000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-227/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c10 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-919617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6844749/10000000) (δ := 8447/1000000000) (ψ := 14699/1000000) 168 62
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t10 : ((-1454121360713/5000000000000 : ℚ) : ℝ) ≤ stT168 10 := by
  have hc : ((-919667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1454121360713/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-919667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c11 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((379883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 221201/1250000) (δ := 4271/500000000) (ψ := 14699/1000000) 168 64
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t11 : ((572657396977/2500000000000 : ℚ) : ℝ) ≤ stT168 11 := by
  have hc : ((189929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572657396977/2500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((189929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c12 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-185569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689847/1000000) (δ := 339/40000000) (ψ := 14699/1000000) 168 66
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t12 : ((-16741267169/62500000000 : ℚ) : ℝ) ≤ stT168 12 := by
  have hc : ((-185579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16741267169/62500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-185579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c13 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-439127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3303743/5000000) (δ := 4203/500000000) (ψ := 14699/1000000) 168 69
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t13 : ((-76124281947/312500000000 : ℚ) : ℝ) ≤ stT168 13 := by
  have hc : ((-27447/31250 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76124281947/312500000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-27447/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c14 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-463891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6898053/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 71
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t14 : ((-309966983127/1250000000000 : ℚ) : ℝ) ≤ stT168 14 := by
  have hc : ((-115979/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-309966983127/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-115979/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c15 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-829161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3185501/5000000) (δ := 1697/200000000) (ψ := 14699/1000000) 168 72
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t15 : ((-2141013680679/10000000000000 : ℚ) : ℝ) ≤ stT168 15 := by
  have hc : ((-829211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2141013680679/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-829211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c16 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((27157/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1030623/5000000) (δ := 8533/1000000000) (ψ := 14699/1000000) 168 74
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t16 : ((5431/32000 : ℚ) : ℝ) ≤ stT168 16 := by
  have hc : ((5431/8000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5431/32000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((5431/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c17 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((433/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3892349/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 76
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t17 : ((4185558117/1250000000000 : ℚ) : ℝ) ≤ stT168 17 := by
  have hc : ((6903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4185558117/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((6903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c18 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-95259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 550777/1250000) (δ := 4227/500000000) (ψ := 14699/1000000) 168 77
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t18 : ((-56146644883/1250000000000 : ℚ) : ℝ) ≤ stT168 18 := by
  have hc : ((-23821/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56146644883/1250000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-23821/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c19 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-149239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4301487/10000000) (δ := 4267/500000000) (ψ := 14699/1000000) 168 79
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t19 : ((-171246276831/5000000000000 : ℚ) : ℝ) ≤ stT168 19 := by
  have hc : ((-149289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171246276831/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-149289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c20 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((817641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191717/1250000) (δ := 8427/1000000000) (ψ := 14699/1000000) 168 80
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t20 : ((1828188254597/10000000000000 : ℚ) : ℝ) ≤ stT168 20 := by
  have hc : ((817591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1828188254597/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((817591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c21 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-163409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6317657/10000000) (δ := 8483/1000000000) (ψ := 14699/1000000) 168 81
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t21 : ((-356609510001/2000000000000 : ℚ) : ℝ) ≤ stT168 21 := by
  have hc : ((-163419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356609510001/2000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-163419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c22 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-151923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -555987/1000000) (δ := 4253/500000000) (ψ := 14699/1000000) 168 83
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t22 : ((-80981925371/625000000000 : ℚ) : ℝ) ≤ stT168 22 := by
  have hc : ((-303871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80981925371/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-303871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c23 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((506883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2598077/10000000) (δ := 1681/200000000) (ψ := 14699/1000000) 168 84
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t23 : ((132102473619/1250000000000 : ℚ) : ℝ) ≤ stT168 23 := by
  have hc : ((506833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132102473619/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((506833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c24 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((39407/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13469/312500) (δ := 133/15625000) (ψ := 14699/1000000) 168 85
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t24 : ((16087020321/80000000000 : ℚ) : ℝ) ≤ stT168 24 := by
  have hc : ((7881/8000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16087020321/80000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((7881/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c25 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((460041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251567/2500000) (δ := 1073/125000000) (ψ := 14699/1000000) 168 86
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t25 : ((28751/156250 : ℚ) : ℝ) ≤ stT168 25 := by
  have hc : ((28751/31250 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28751/156250 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((28751/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c26 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((189851/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1770999/10000000) (δ := 8477/1000000000) (ψ := 14699/1000000) 168 87
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t26 : ((744607724997/5000000000000 : ℚ) : ℝ) ≤ stT168 26 := by
  have hc : ((379677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((744607724997/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((379677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c27 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((720977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 956981/5000000) (δ := 8433/1000000000) (ψ := 14699/1000000) 168 88
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t27 : ((2774848023/20000000000 : ℚ) : ℝ) ≤ stT168 27 := by
  have hc : ((720927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2774848023/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((720927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c28 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((82973/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1480433/10000000) (δ := 427/50000000) (ψ := 14699/1000000) 168 89
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t28 : ((9799671981/62500000000 : ℚ) : ℝ) ≤ stT168 28 := by
  have hc : ((10371/12500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9799671981/62500000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((10371/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c29 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((489599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102163/2000000) (δ := 1711/200000000) (ψ := 14699/1000000) 168 90
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t29 : ((454557954011/2500000000000 : ℚ) : ℝ) ≤ stT168 29 := by
  have hc : ((244787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454557954011/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((244787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c30 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((185479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479259/5000000) (δ := 33/3906250) (ψ := 14699/1000000) 168 91
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t30 : ((338618357529/2000000000000 : ℚ) : ℝ) ≤ stT168 30 := by
  have hc : ((185469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338618357529/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((185469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c31 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((200637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2894723/10000000) (δ := 4231/500000000) (ψ := 14699/1000000) 168 92
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t31 : ((90077446109/1250000000000 : ℚ) : ℝ) ≤ stT168 31 := by
  have hc : ((50153/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90077446109/1250000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((50153/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c32 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-63891/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -658529/1250000) (δ := 8569/1000000000) (ψ := 14699/1000000) 168 93
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t32 : ((-451821799763/5000000000000 : ℚ) : ℝ) ≤ stT168 32 := by
  have hc : ((-255589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451821799763/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-255589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c33 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-996861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47849/62500) (δ := 8569/1000000000) (ψ := 14699/1000000) 168 93
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t33 : ((-1735399739847/10000000000000 : ℚ) : ℝ) ≤ stT168 33 := by
  have hc : ((-996911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1735399739847/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-996911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c34 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-110899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 560767/1250000) (δ := 8527/1000000000) (ψ := 14699/1000000) 168 94
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t34 : ((-23779138383/625000000000 : ℚ) : ℝ) ≤ stT168 34 := by
  have hc : ((-27731/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23779138383/625000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-27731/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c35 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((92823/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 952923/10000000) (δ := 8419/1000000000) (ψ := 14699/1000000) 168 95
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t35 : ((19611375993/125000000000 : ℚ) : ℝ) ≤ stT168 35 := by
  have hc : ((46409/50000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19611375993/125000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((46409/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c36 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((48849/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1461631/5000000) (δ := 8491/1000000000) (ψ := 14699/1000000) 168 96
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t36 : ((162809101543/2500000000000 : ℚ) : ℝ) ≤ stT168 36 := by
  have hc : ((195371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162809101543/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((195371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c37 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-957631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1424729/2000000) (δ := 4299/500000000) (ψ := 14699/1000000) 168 97
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t37 : ((-157441798719/1000000000000 : ℚ) : ℝ) ≤ stT168 37 := by
  have hc : ((-957681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157441798719/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-957681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c38 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-59967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4076999/10000000) (δ := 4299/500000000) (ψ := 14699/1000000) 168 97
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t38 : ((-19472095531/2000000000000 : ℚ) : ℝ) ≤ stT168 38 := by
  have hc : ((-60017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19472095531/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-60017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c39 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((958671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144251/2000000) (δ := 4249/500000000) (ψ := 14699/1000000) 168 98
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t39 : ((1535021593501/10000000000000 : ℚ) : ℝ) ≤ stT168 39 := by
  have hc : ((958621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1535021593501/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((958621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c40 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-10622/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2897871/5000000) (δ := 2103/250000000) (ψ := 14699/1000000) 168 99
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t40 : ((-537474999131/5000000000000 : ℚ) : ℝ) ≤ stT168 40 := by
  have hc : ((-339929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537474999131/5000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-339929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c41 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-256369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91503/200000) (δ := 2103/250000000) (ψ := 14699/1000000) 168 99
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t41 : ((-200229648111/5000000000000 : ℚ) : ℝ) ≤ stT168 41 := by
  have hc : ((-256419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200229648111/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-256419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c42 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((919209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1011821/10000000) (δ := 8519/1000000000) (ψ := 14699/1000000) 168 100
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t42 : ((1418292669247/10000000000000 : ℚ) : ℝ) ≤ stT168 42 := by
  have hc : ((919159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1418292669247/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((919159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c43 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-918391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -273479/400000) (δ := 67/7812500) (ψ := 14699/1000000) 168 101
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t43 : ((-700304833413/5000000000000 : ℚ) : ℝ) ≤ stT168 43 := by
  have hc : ((-918441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-700304833413/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-918441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c44 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((53621/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 563723/2000000) (δ := 67/7812500) (ψ := 14699/1000000) 168 101
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t44 : ((80827238051/1250000000000 : ℚ) : ℝ) ≤ stT168 44 := by
  have hc : ((214459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80827238051/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((214459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c45 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((94669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -862693/2500000) (δ := 8469/1000000000) (ψ := 14699/1000000) 168 102
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t45 : ((35271712971/1250000000000 : ℚ) : ℝ) ≤ stT168 45 := by
  have hc : ((23661/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35271712971/1250000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((23661/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c46 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-168821/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2890183/5000000) (δ := 8469/1000000000) (ψ := 14699/1000000) 168 102
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t46 : ((-24893148907/250000000000 : ℚ) : ℝ) ≤ stT168 46 := by
  have hc : ((-337667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24893148907/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-337667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c47 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((468303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -894951/10000000) (δ := 8441/1000000000) (ψ := 14699/1000000) 168 103
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t47 : ((341526618211/2500000000000 : ℚ) : ℝ) ≤ stT168 47 := by
  have hc : ((234139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341526618211/2500000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((234139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c48 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-999301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3880243/5000000) (δ := 2137/250000000) (ψ := 14699/1000000) 168 104
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t48 : ((-90152453061/625000000000 : ℚ) : ℝ) ≤ stT168 48 := by
  have hc : ((-999351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90152453061/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-999351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c49 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((233989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 449789/5000000) (δ := 2137/250000000) (ψ := 14699/1000000) 168 104
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t49 : ((668504085163/5000000000000 : ℚ) : ℝ) ≤ stT168 49 := by
  have hc : ((467953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((668504085163/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((467953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c50 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-818323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -632321/1000000) (δ := 2137/250000000) (ψ := 14699/1000000) 168 105
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t50 : ((-578677276911/5000000000000 : ℚ) : ℝ) ≤ stT168 50 := by
  have hc : ((-818373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-578677276911/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-818373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c51 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((34923/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 996941/5000000) (δ := 2137/250000000) (ψ := 14699/1000000) 168 105
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t51 : ((2444923887/25000000000 : ℚ) : ℝ) ≤ stT168 51 := by
  have hc : ((69841/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2444923887/25000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((69841/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c52 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-2429/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5558479/10000000) (δ := 211/25000000) (ψ := 14699/1000000) 168 106
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t52 : ((-8421738823/100000000000 : ℚ) : ℝ) ≤ stT168 52 := by
  have hc : ((-6073/10000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8421738823/100000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-6073/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c53 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((111951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 488353/2000000) (δ := 211/25000000) (ψ := 14699/1000000) 168 106
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t53 : ((30752543461/400000000000 : ℚ) : ℝ) ≤ stT168 53 := by
  have hc : ((111941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30752543461/400000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((111941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c54 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-35053/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353879/2500000) (δ := 847/100000000) (ψ := 14699/1000000) 168 107
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t54 : ((-95410712943/1250000000000 : ℚ) : ℝ) ≤ stT168 54 := by
  have hc : ((-280449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95410712943/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-280449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c55 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((608647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145553/5000000) (δ := 847/100000000) (ψ := 14699/1000000) 168 107
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t55 : ((820631586203/10000000000000 : ℚ) : ℝ) ≤ stT168 55 := by
  have hc : ((608597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((820631586203/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((608597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c56 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-695301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5849087/10000000) (δ := 8577/1000000000) (ψ := 14699/1000000) 168 108
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t56 : ((-929202408757/10000000000000 : ℚ) : ℝ) ≤ stT168 56 := by
  have hc : ((-695351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-929202408757/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-695351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c57 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((32229/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316949/2000000) (δ := 8577/1000000000) (ψ := 14699/1000000) 168 108
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t57 : ((10671423191/100000000000 : ℚ) : ℝ) ≤ stT168 57 := by
  have hc : ((32227/40000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10671423191/100000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((32227/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c58 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-228867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6818663/10000000) (δ := 8519/1000000000) (ψ := 14699/1000000) 168 109
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t58 : ((-120213464267/1000000000000 : ℚ) : ℝ) ≤ stT168 58 := by
  have hc : ((-457759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120213464267/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-457759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c59 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((989593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72197/2000000) (δ := 8519/1000000000) (ψ := 14699/1000000) 168 109
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t59 : ((1288275146727/10000000000000 : ℚ) : ℝ) ≤ stT168 59 := by
  have hc : ((989543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1288275146727/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((989543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c60 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-123121/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7419967/10000000) (δ := 8519/1000000000) (ψ := 14699/1000000) 168 109
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t60 : ((-127165331291/1000000000000 : ℚ) : ℝ) ≤ stT168 60 := by
  have hc : ((-492509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127165331291/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-492509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c61 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((429297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -134569/1000000) (δ := 2103/250000000) (ψ := 14699/1000000) 168 110
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t61 : ((4293954157/39062500000 : ℚ) : ℝ) ≤ stT168 61 := by
  have hc : ((53659/62500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4293954157/39062500000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((53659/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c62 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-72903/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137093/250000) (δ := 2103/250000000) (ψ := 14699/1000000) 168 110
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t62 : ((-185189786637/2500000000000 : ℚ) : ℝ) ≤ stT168 62 := by
  have hc : ((-291637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185189786637/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-291637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c63 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((168361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140163/400000) (δ := 4249/500000000) (ψ := 14699/1000000) 168 111
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t63 : ((212051830991/10000000000000 : ℚ) : ℝ) ≤ stT168 63 := by
  have hc : ((168311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212051830991/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((168311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c64 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((320931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3110211/10000000) (δ := 4249/500000000) (ψ := 14699/1000000) 168 111
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t64 : ((320881/8000000 : ℚ) : ℝ) ≤ stT168 64 := by
  have hc : ((320881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320881/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((320881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c65 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-380093/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6085989/10000000) (δ := 8597/1000000000) (ψ := 14699/1000000) 168 112
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t65 : ((-58934825133/625000000000 : ℚ) : ℝ) ≤ stT168 65 := by
  have hc : ((-190059/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58934825133/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-190059/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c66 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((991491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326361/10000000) (δ := 8597/1000000000) (ψ := 14699/1000000) 168 112
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t66 : ((610189303537/5000000000000 : ℚ) : ℝ) ≤ stT168 66 := by
  have hc : ((991441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((610189303537/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((991441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c67 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-110603/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6642279/10000000) (δ := 8597/1000000000) (ψ := 14699/1000000) 168 112
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t67 : ((-108104614143/1000000000000 : ℚ) : ℝ) ≤ stT168 67 := by
  have hc : ((-442437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108104614143/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-442437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c68 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((420013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1421671/5000000) (δ := 849/100000000) (ψ := 14699/1000000) 168 113
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t68 : ((254639945457/5000000000000 : ℚ) : ℝ) ≤ stT168 68 := by
  have hc : ((419963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254639945457/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((419963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c69 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((252763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1644077/5000000) (δ := 849/100000000) (ψ := 14699/1000000) 168 113
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t69 : ((152115283377/5000000000000 : ℚ) : ℝ) ≤ stT168 69 := by
  have hc : ((252713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152115283377/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((252713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c70 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-519/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1275311/2000000) (δ := 421/50000000) (ψ := 14699/1000000) 168 114
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t70 : ((-19851558461/200000000000 : ℚ) : ℝ) ≤ stT168 70 := by
  have hc : ((-16609/20000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19851558461/200000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-16609/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c71 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((492993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419023/10000000) (δ := 421/50000000) (ψ := 14699/1000000) 168 114
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t71 : ((73130632001/625000000000 : ℚ) : ℝ) ≤ stT168 71 := by
  have hc : ((61621/62500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73130632001/625000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((61621/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c72 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-573927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5455223/10000000) (δ := 421/50000000) (ψ := 14699/1000000) 168 114
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t72 : ((-42277423889/625000000000 : ℚ) : ℝ) ≤ stT168 72 := by
  have hc : ((-573977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42277423889/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-573977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c73 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-105709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2229777/5000000) (δ := 8527/1000000000) (ψ := 14699/1000000) 168 115
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t73 : ((-15469042801/625000000000 : ℚ) : ℝ) ≤ stT168 73 := by
  have hc : ((-52867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15469042801/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-52867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c74 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((876661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 627399/5000000) (δ := 8527/1000000000) (ψ := 14699/1000000) 168 115
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t74 : ((254759812209/2500000000000 : ℚ) : ℝ) ≤ stT168 74 := by
  have hc : ((876611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254759812209/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((876611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c75 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-926951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2757/4000) (δ := 8527/1000000000) (ψ := 14699/1000000) 168 115
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t75 : ((-1070408981701/10000000000000 : ℚ) : ℝ) ≤ stT168 75 := by
  have hc : ((-927001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1070408981701/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-927001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c76 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((266543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5082/15625) (δ := 8569/1000000000) (ψ := 14699/1000000) 168 116
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t76 : ((152844128727/5000000000000 : ℚ) : ℝ) ≤ stT168 76 := by
  have hc : ((266493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152844128727/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((266493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c77 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((25017/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1118901/5000000) (δ := 8569/1000000000) (ψ := 14699/1000000) 168 116
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t77 : ((1140288763/16000000000 : ℚ) : ℝ) ≤ stT168 77 := by
  have hc : ((5003/8000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1140288763/16000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((5003/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c78 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-199381/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 765723/1000000) (δ := 8569/1000000000) (ψ := 14699/1000000) 168 116
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t78 : ((-112883021349/1000000000000 : ℚ) : ℝ) ≤ stT168 78 := by
  have hc : ((-199391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112883021349/1000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-199391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c79 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((117801/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2700353/10000000) (δ := 8461/1000000000) (ψ := 14699/1000000) 168 117
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t79 : ((265044620199/5000000000000 : ℚ) : ℝ) ≤ stT168 79 := by
  have hc : ((235577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265044620199/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((235577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c80 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((512161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2582743/10000000) (δ := 8461/1000000000) (ψ := 14699/1000000) 168 117
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t80 : ((572556997663/10000000000000 : ℚ) : ℝ) ≤ stT168 80 := by
  have hc : ((512111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572556997663/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((512111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c81 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-999769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7800193/10000000) (δ := 8461/1000000000) (ψ := 14699/1000000) 168 117
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t81 : ((-138863861091/1250000000000 : ℚ) : ℝ) ≤ stT168 81 := by
  have hc : ((-999819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138863861091/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-999819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c82 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((452053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -344291/1250000) (δ := 8449/1000000000) (ψ := 14699/1000000) 168 118
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t82 : ((99830738589/2000000000000 : ℚ) : ℝ) ≤ stT168 82 := by
  have hc : ((452003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99830738589/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((452003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c83 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((594089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 116833/500000) (δ := 8449/1000000000) (ψ := 14699/1000000) 168 118
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t83 : ((326021078019/5000000000000 : ℚ) : ℝ) ≤ stT168 83 := by
  have hc : ((594039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326021078019/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((594039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c84 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-49053/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7366643/10000000) (δ := 16849/1000000000) (ψ := 14699/1000000) 168 118
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t84 : ((-10704793099/100000000000 : ℚ) : ℝ) ≤ stT168 84 := by
  have hc : ((-98111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10704793099/100000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-98111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c85 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((110313/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3370851/10000000) (δ := 2139/250000000) (ψ := 14699/1000000) 168 119
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t85 : ((1869126559/78125000000 : ℚ) : ℝ) ≤ stT168 85 := by
  have hc : ((6893/31250 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1869126559/78125000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((6893/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c86 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((50991/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1541469/10000000) (δ := 2139/250000000) (ψ := 14699/1000000) 168 119
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t86 : ((439852818281/5000000000000 : ℚ) : ℝ) ≤ stT168 86 := by
  have hc : ((407903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439852818281/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((407903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c87 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-834939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6397047/10000000) (δ := 2139/250000000) (ψ := 14699/1000000) 168 119
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t87 : ((-895202561757/10000000000000 : ℚ) : ℝ) ≤ stT168 87 := by
  have hc : ((-834989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-895202561757/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-834989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c88 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-231431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4510863/10000000) (δ := 427/50000000) (ψ := 14699/1000000) 168 120
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t88 : ((-61689917981/2500000000000 : ℚ) : ℝ) ≤ stT168 88 := by
  have hc : ((-231481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61689917981/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-231481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c89 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((248897/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 234927/10000000) (δ := 427/50000000) (ψ := 14699/1000000) 168 120
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t89 : ((527633646693/5000000000000 : ℚ) : ℝ) ≤ stT168 89 := by
  have hc : ((497769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527633646693/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((497769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c90 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-97421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4927713/10000000) (δ := 427/50000000) (ψ := 14699/1000000) 168 120
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t90 : ((-205407940631/5000000000000 : ℚ) : ℝ) ≤ stT168 90 := by
  have hc : ((-194867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205407940631/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-194867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c91 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-77387/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6139313/10000000) (δ := 16833/1000000000) (ψ := 14699/1000000) 168 121
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t91 : ((-1014110909/12500000000 : ℚ) : ℝ) ≤ stT168 91 := by
  have hc : ((-4837/6250 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1014110909/12500000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-4837/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c92 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((162817/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193639/1250000) (δ := 8433/1000000000) (ψ := 14699/1000000) 168 121
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t92 : ((42434504901/500000000000 : ℚ) : ℝ) ≤ stT168 92 := by
  have hc : ((162807/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42434504901/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((162807/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c93 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((365537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1495733/5000000) (δ := 8433/1000000000) (ψ := 14699/1000000) 168 121
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t93 : ((378992110137/10000000000000 : ℚ) : ℝ) ≤ stT168 93 := by
  have hc : ((365487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((378992110137/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((365487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c94 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-989039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1870873/2500000) (δ := 8433/1000000000) (ψ := 14699/1000000) 168 121
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t94 : ((-510084077279/5000000000000 : ℚ) : ℝ) ≤ stT168 94 := by
  have hc : ((-989089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-510084077279/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-989089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c95 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((58767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3779989/10000000) (δ := 8477/1000000000) (ψ := 14699/1000000) 168 122
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t95 : ((30121175113/5000000000000 : ℚ) : ℝ) ≤ stT168 95 := by
  have hc : ((58717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30121175113/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((58717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c96 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((484803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617957/10000000) (δ := 8477/1000000000) (ψ := 14699/1000000) 168 122
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t96 : ((12369353059/125000000000 : ℚ) : ℝ) ≤ stT168 96 := by
  have hc : ((242389/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12369353059/125000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((242389/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c97 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-405327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4970333/10000000) (δ := 8477/1000000000) (ψ := 14699/1000000) 168 122
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t97 : ((-411598320819/10000000000000 : ℚ) : ℝ) ≤ stT168 97 := by
  have hc : ((-405377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-411598320819/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-405377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c98 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-842099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -64299/100000) (δ := 1717/200000000) (ψ := 14699/1000000) 168 123
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t98 : ((-850699338797/10000000000000 : ℚ) : ℝ) ≤ stT168 98 := by
  have hc : ((-842149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-850699338797/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-842149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c99 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((647607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541473/2500000) (δ := 1717/200000000) (ψ := 14699/1000000) 168 123
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t99 : ((650818744609/10000000000000 : ℚ) : ℝ) ≤ stT168 99 := by
  have hc : ((647557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650818744609/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((647557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c100 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((680689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1027617/5000000) (δ := 1717/200000000) (ψ := 14699/1000000) 168 123
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t100 : ((680638319361/10000000000000 : ℚ) : ℝ) ≤ stT168 100 := by
  have hc : ((680639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((680638319361/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((680639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c101 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-398697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3117201/5000000) (δ := 1717/200000000) (ψ := 14699/1000000) 168 123
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t101 : ((-99185885359/1250000000000 : ℚ) : ℝ) ≤ stT168 101 := by
  have hc : ((-199361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99185885359/1250000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-199361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c102 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-534099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1333899/2500000) (δ := 8511/1000000000) (ψ := 14699/1000000) 168 124
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t102 : ((-132221641013/2500000000000 : ℚ) : ℝ) ≤ stT168 102 := by
  have hc : ((-534149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132221641013/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-534149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c103 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((879867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619017/5000000) (δ := 8511/1000000000) (ψ := 14699/1000000) 168 124
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t103 : ((866909204793/10000000000000 : ℚ) : ℝ) ≤ stT168 103 := by
  have hc : ((879817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((866909204793/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((879817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c104 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((428481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 704991/2500000) (δ := 8511/1000000000) (ψ := 14699/1000000) 168 124
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t104 : ((21005543499/500000000000 : ℚ) : ℝ) ≤ stT168 104 := by
  have hc : ((428431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21005543499/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((428431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c105 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-183747/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3419577/5000000) (δ := 8511/1000000000) (ψ := 14699/1000000) 168 124
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t105 : ((-179328640057/2000000000000 : ℚ) : ℝ) ≤ stT168 105 := by
  have hc : ((-183757/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179328640057/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-183757/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c106 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-93729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -977551/2000000) (δ := 2101/250000000) (ψ := 14699/1000000) 168 125
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t106 : ((-91049806569/2500000000000 : ℚ) : ℝ) ≤ stT168 106 := by
  have hc : ((-187483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91049806569/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-187483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c107 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((464773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -944039/10000000) (δ := 2101/250000000) (ψ := 14699/1000000) 168 125
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t107 : ((7020134727/78125000000 : ℚ) : ℝ) ≤ stT168 107 := by
  have hc : ((116187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7020134727/78125000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((116187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c108 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((376123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2962969/10000000) (δ := 2101/250000000) (ψ := 14699/1000000) 168 125
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t108 : ((1447504977/40000000000 : ℚ) : ℝ) ≤ stT168 108 := by
  have hc : ((376073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1447504977/40000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((376073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c109 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-91791/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6833941/10000000) (δ := 2101/250000000) (ψ := 14699/1000000) 168 125
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t109 : ((-21981171823/250000000000 : ℚ) : ℝ) ≤ stT168 109 := by
  have hc : ((-22949/25000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21981171823/250000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-22949/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c110 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-215027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1259593/2500000) (δ := 4253/500000000) (ψ := 14699/1000000) 168 126
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t110 : ((-51261031269/1250000000000 : ℚ) : ℝ) ≤ stT168 110 := by
  have hc : ((-53763/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51261031269/1250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-53763/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c111 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((175997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618707/5000000) (δ := 4253/500000000) (ψ := 14699/1000000) 168 126
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t111 : ((167039292959/2000000000000 : ℚ) : ℝ) ≤ stT168 111 := by
  have hc : ((175987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167039292959/2000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((175987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c112 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((53037/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264699/5000000) (δ := 4253/500000000) (ψ := 14699/1000000) 168 126
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t112 : ((6263815019/125000000000 : ℚ) : ℝ) ≤ stT168 112 := by
  have hc : ((6629/12500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6263815019/125000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((6629/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c113 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-25131/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3131389/5000000) (δ := 4253/500000000) (ψ := 14699/1000000) 168 126
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t113 : ((-378283669241/5000000000000 : ℚ) : ℝ) ≤ stT168 113 := by
  have hc : ((-402121/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378283669241/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-402121/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c114 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-10386/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2872367/5000000) (δ := 859/100000000) (ψ := 14699/1000000) 168 127
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t114 : ((-155649822461/2500000000000 : ℚ) : ℝ) ≤ stT168 114 := by
  have hc : ((-332377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155649822461/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-332377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c115 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((674409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -103829/500000) (δ := 859/100000000) (ψ := 14699/1000000) 168 127
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t115 : ((78605308117/1250000000000 : ℚ) : ℝ) ≤ stT168 115 := by
  have hc : ((674359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78605308117/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((674359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c116 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((811599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77989/500000) (δ := 859/100000000) (ψ := 14699/1000000) 168 127
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t116 : ((188375942331/2500000000000 : ℚ) : ℝ) ≤ stT168 116 := by
  have hc : ((811549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188375942331/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((811549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c117 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-237601/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322811/625000) (δ := 859/100000000) (ψ := 14699/1000000) 168 127
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t117 : ((-109842737313/2500000000000 : ℚ) : ℝ) ≤ stT168 117 := by
  have hc : ((-118813/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109842737313/2500000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-118813/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c118 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-468963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6968493/10000000) (δ := 8483/1000000000) (ψ := 14699/1000000) 168 128
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t118 : ((-4317386281/50000000000 : ℚ) : ℝ) ≤ stT168 118 := by
  have hc : ((-117247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4317386281/50000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-117247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c119 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((49941/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3424197/10000000) (δ := 8483/1000000000) (ψ := 14699/1000000) 168 128
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t119 : ((45769356093/2500000000000 : ℚ) : ℝ) ≤ stT168 119 := by
  have hc : ((99857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45769356093/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((99857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c120 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((199869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90489/10000000) (δ := 8483/1000000000) (ψ := 14699/1000000) 168 128
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t120 : ((18244528533/200000000000 : ℚ) : ℝ) ≤ stT168 120 := by
  have hc : ((199859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18244528533/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((199859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c121 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((139941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 715197/2000000) (δ := 8483/1000000000) (ψ := 14699/1000000) 168 128
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t121 : ((12717350919/1000000000000 : ℚ) : ℝ) ≤ stT168 121 := by
  have hc : ((139891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12717350919/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((139891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c122 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-118317/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1406559/2000000) (δ := 8483/1000000000) (ψ := 14699/1000000) 168 128
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t122 : ((-214249801947/2500000000000 : ℚ) : ℝ) ≤ stT168 122 := by
  have hc : ((-473293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214249801947/2500000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-473293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c123 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-100733/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2623291/5000000) (δ := 2107/250000000) (ψ := 14699/1000000) 168 129
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t123 : ((-9083694081/200000000000 : ℚ) : ℝ) ≤ stT168 123 := by
  have hc : ((-100743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9083694081/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-100743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c124 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((184903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922879/5000000) (δ := 2107/250000000) (ψ := 14699/1000000) 168 129
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t124 : ((166036476153/2500000000000 : ℚ) : ℝ) ≤ stT168 124 := by
  have hc : ((369781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166036476153/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((369781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c125 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((409507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 763883/5000000) (δ := 2107/250000000) (ψ := 14699/1000000) 168 129
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t125 : ((183125878407/2500000000000 : ℚ) : ℝ) ≤ stT168 125 := by
  have hc : ((204741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183125878407/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((204741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c126 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-184981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 487441/1000000) (δ := 2107/250000000) (ψ := 14699/1000000) 168 129
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t126 : ((-82408240113/2500000000000 : ℚ) : ℝ) ≤ stT168 126 := by
  have hc : ((-92503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82408240113/2500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-92503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c127 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-198147/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7513411/10000000) (δ := 1707/200000000) (ψ := 14699/1000000) 168 130
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t127 : ((-175836001049/2000000000000 : ℚ) : ℝ) ≤ stT168 127 := by
  have hc : ((-198157/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175836001049/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-198157/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c128 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-29161/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4219267/10000000) (δ := 1707/200000000) (ψ := 14699/1000000) 168 130
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t128 : ((-12892994937/1250000000000 : ℚ) : ℝ) ≤ stT168 128 := by
  have hc : ((-58347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12892994937/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-58347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c129 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((464277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -950743/10000000) (δ := 1707/200000000) (ψ := 14699/1000000) 168 130
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t129 : ((2043753367/25000000000 : ℚ) : ℝ) ≤ stT168 129 := by
  have hc : ((116063/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2043753367/25000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((116063/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c130 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((121641/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2292497/10000000) (δ := 1707/200000000) (ψ := 14699/1000000) 168 130
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t130 : ((53338720799/1000000000000 : ℚ) : ℝ) ≤ stT168 130 := by
  have hc : ((121631/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53338720799/1000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((121631/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c131 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-23681/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1102183/2000000) (δ := 1707/200000000) (ψ := 14699/1000000) 168 130
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t131 : ((-4138391103/80000000000 : ℚ) : ℝ) ≤ stT168 131 := by
  have hc : ((-23683/40000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4138391103/80000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-23683/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c132 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-942639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7003117/10000000) (δ := 8561/1000000000) (ψ := 14699/1000000) 168 131
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t132 : ((-820506136021/10000000000000 : ℚ) : ℝ) ≤ stT168 132 := by
  have hc : ((-942689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820506136021/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-942689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c133 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((3747/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3833293/10000000) (δ := 8561/1000000000) (ψ := 14699/1000000) 168 131
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t133 : ((1622360939/500000000000 : ℚ) : ℝ) ≤ stT168 133 := by
  have hc : ((1871/50000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1622360939/500000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((1871/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c134 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((120307/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34361/500000) (δ := 16961/1000000000) (ψ := 14699/1000000) 168 131
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t134 : ((103923968301/1250000000000 : ℚ) : ℝ) ≤ stT168 134 := by
  have hc : ((481203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103923968301/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((481203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c135 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((140461/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2435459/10000000) (δ := 8561/1000000000) (ψ := 14699/1000000) 168 131
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t135 : ((120878686907/2500000000000 : ℚ) : ℝ) ≤ stT168 135 := by
  have hc : ((280897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120878686907/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((280897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c136 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-299897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5535101/10000000) (δ := 8561/1000000000) (ψ := 14699/1000000) 168 131
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t136 : ((-128590507773/2500000000000 : ℚ) : ℝ) ≤ stT168 136 := by
  have hc : ((-149961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128590507773/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-149961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c137 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-119297/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70959/100000) (δ := 4227/500000000) (ψ := 14699/1000000) 168 132
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t137 : ((-203855372127/2500000000000 : ℚ) : ℝ) ≤ stT168 137 := by
  have hc : ((-477213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203855372127/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-477213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c138 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-22867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2020683/5000000) (δ := 4227/500000000) (ψ := 14699/1000000) 168 132
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t138 : ((-4871743811/1250000000000 : ℚ) : ℝ) ≤ stT168 138 := by
  have hc : ((-5723/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4871743811/1250000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-5723/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c139 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((459839/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25221/250000) (δ := 4227/500000000) (ψ := 14699/1000000) 168 132
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t139 : ((48751089629/625000000000 : ℚ) : ℝ) ≤ stT168 139 := by
  have hc : ((229907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48751089629/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((229907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c140 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((696153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 200193/1000000) (δ := 4227/500000000) (ψ := 14699/1000000) 168 132
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t140 : ((294157117431/5000000000000 : ℚ) : ℝ) ≤ stT168 140 := by
  have hc : ((696103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294157117431/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((696103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c141 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-412957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2495619/5000000) (δ := 4227/500000000) (ψ := 14699/1000000) 168 132
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t141 : ((-43476833883/1250000000000 : ℚ) : ℝ) ≤ stT168 141 := by
  have hc : ((-413007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43476833883/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-413007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c142 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-99911/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7748501/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 133
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t142 : ((-10480963589/125000000000 : ℚ) : ℝ) ≤ stT168 142 := by
  have hc : ((-24979/25000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10480963589/125000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-24979/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c143 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-171283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4801109/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 133
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t143 : ((-35813778961/1250000000000 : ℚ) : ℝ) ≤ stT168 143 := by
  have hc : ((-42827/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35813778961/1250000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-42827/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c144 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((731881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1874297/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 133
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t144 : ((609858922723/10000000000000 : ℚ) : ℝ) ≤ stT168 144 := by
  have hc : ((731831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((609858922723/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((731831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c145 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((915951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032313/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 133
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t145 : ((380306824527/5000000000000 : ℚ) : ℝ) ≤ stT168 145 := by
  have hc : ((915901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380306824527/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((915901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c146 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((403/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3918931/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 133
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t146 : ((262681827/1000000000000 : ℚ) : ℝ) ≤ stT168 146 := by
  have hc : ((1587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((262681827/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((1587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c147 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-910101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6785809/10000000) (δ := 1057/125000000) (ψ := 14699/1000000) 168 133
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t147 : ((-750680712837/10000000000000 : ℚ) : ℝ) ≤ stT168 147 := by
  have hc : ((-910151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750680712837/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-910151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c148 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-757239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -151867/250000) (δ := 2141/250000000) (ψ := 14699/1000000) 168 134
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t148 : ((-124497554311/2000000000000 : ℚ) : ℝ) ≤ stT168 148 := by
  have hc : ((-757289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124497554311/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-757289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c149 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((134451/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1623179/5000000) (δ := 2141/250000000) (ψ := 14699/1000000) 168 134
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t149 : ((55062973203/2500000000000 : ℚ) : ℝ) ≤ stT168 149 := by
  have hc : ((67213/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55062973203/2500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((67213/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c150 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((24619/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21851/500000) (δ := 2141/250000000) (ψ := 14699/1000000) 168 134
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t150 : ((5025073601/62500000000 : ℚ) : ℝ) ≤ stT168 150 := by
  have hc : ((98471/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5025073601/62500000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((98471/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c151 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((147147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147107/625000) (δ := 2141/250000000) (ψ := 14699/1000000) 168 134
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t151 : ((59868145243/1250000000000 : ℚ) : ℝ) ≤ stT168 151 := by
  have hc : ((294269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59868145243/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((294269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c152 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-46143/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2563003/5000000) (δ := 2141/250000000) (ψ := 14699/1000000) 168 134
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t152 : ((-2339438249/62500000000 : ℚ) : ℝ) ≤ stT168 152 := by
  have hc : ((-11537/25000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2339438249/62500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-11537/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c153 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-199989/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156557/200000) (δ := 2133/250000000) (ψ := 14699/1000000) 168 135
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t153 : ((-161689791547/2000000000000 : ℚ) : ℝ) ≤ stT168 153 := by
  have hc : ((-199999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161689791547/2000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-199999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c154 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-112301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1272919/2500000) (δ := 2133/250000000) (ψ := 14699/1000000) 168 135
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t154 : ((-181009603021/5000000000000 : ℚ) : ℝ) ≤ stT168 154 := by
  have hc : ((-224627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-181009603021/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-224627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c155 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((29113/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1186613/5000000) (δ := 2133/250000000) (ψ := 14699/1000000) 168 135
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t155 : ((46764213399/1000000000000 : ℚ) : ℝ) ≤ stT168 155 := by
  have hc : ((58221/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46764213399/1000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((58221/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c156 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((991419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40969/1250000) (δ := 2133/250000000) (ψ := 14699/1000000) 168 135
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t156 : ((1240202619/15625000000 : ℚ) : ℝ) ≤ stT168 156 := by
  have hc : ((991369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1240202619/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((991369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c157 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((358079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 752867/2500000) (δ := 2133/250000000) (ψ := 14699/1000000) 168 135
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t157 : ((142868966247/5000000000000 : ℚ) : ℝ) ≤ stT168 157 := by
  have hc : ((358029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142868966247/5000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((358029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c158 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-644567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1419533/2500000) (δ := 2133/250000000) (ψ := 14699/1000000) 168 135
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t158 : ((-256415105643/5000000000000 : ℚ) : ℝ) ≤ stT168 158 := by
  have hc : ((-644617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256415105643/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-644617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c159 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-982079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7379967/10000000) (δ := 337/40000000) (ψ := 14699/1000000) 168 136
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t159 : ((-194719841927/2500000000000 : ℚ) : ℝ) ≤ stT168 159 := by
  have hc : ((-982129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194719841927/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-982129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c160 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-322053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -949347/2000000) (δ := 337/40000000) (ψ := 14699/1000000) 168 136
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t160 : ((-25464496871/1000000000000 : ℚ) : ℝ) ≤ stT168 160 := by
  have hc : ((-322103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25464496871/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-322103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c161 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((329251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85197/400000) (δ := 337/40000000) (ψ := 14699/1000000) 168 136
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t161 : ((12973315143/250000000000 : ℚ) : ℝ) ≤ stT168 161 := by
  have hc : ((164613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12973315143/250000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((164613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c162 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((491163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94143/2000000) (δ := 337/40000000) (ψ := 14699/1000000) 168 136
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t162 : ((96468589253/1250000000000 : ℚ) : ℝ) ≤ stT168 162 := by
  have hc : ((245569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96468589253/1250000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((245569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c163 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((170817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3055353/10000000) (δ := 337/40000000) (ψ := 14699/1000000) 168 136
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t163 : ((836090887/31250000000 : ℚ) : ℝ) ≤ stT168 163 := by
  have hc : ((21349/62500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((836090887/31250000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((21349/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c164 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-627911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5624157/10000000) (δ := 337/40000000) (ψ := 14699/1000000) 168 136
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t164 : ((-490355278109/10000000000000 : ℚ) : ℝ) ≤ stT168 164 := by
  have hc : ((-627961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-490355278109/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-627961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c165 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-991647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3765313/5000000) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t165 : ((-772035122803/10000000000000 : ℚ) : ℝ) ≤ stT168 165 := by
  have hc : ((-991697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772035122803/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-991697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c166 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-103387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249643/500000) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t166 : ((-160507250649/5000000000000 : ℚ) : ℝ) ≤ stT168 166 := by
  have hc : ((-206799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160507250649/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-206799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c167 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((550261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1235149/5000000) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t167 : ((425765926653/10000000000000 : ℚ) : ℝ) ≤ stT168 167 := by
  have hc : ((550211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((425765926653/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((550211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c168 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((99989/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4643/1250000) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t168 : ((1205300871/15625000000 : ℚ) : ℝ) ≤ stT168 168 := by
  have hc : ((6249/6250 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1205300871/15625000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((6249/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c169 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((530247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15811/62500) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t169 : ((40784343831/1000000000000 : ℚ) : ℝ) ≤ stT168 169 := by
  have hc : ((530197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40784343831/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((530197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c170 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-209461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2503817/5000000) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t170 : ((-16066842999/500000000000 : ℚ) : ℝ) ≤ stT168 170 := by
  have hc : ((-104743/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16066842999/500000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-104743/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c171 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-988287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58367/78125) (δ := 1697/200000000) (ψ := 14699/1000000) 168 137
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t171 : ((-9447513383/125000000000 : ℚ) : ℝ) ≤ stT168 171 := by
  have hc : ((-988337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9447513383/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-988337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c172 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-21173/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5788009/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 138
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t172 : ((-258327290949/5000000000000 : ℚ) : ℝ) ≤ stT168 172 := by
  have hc : ((-338793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258327290949/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-338793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c173 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((28437/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3353227/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 138
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t173 : ((17292378211/1000000000000 : ℚ) : ℝ) ≤ stT168 173 := by
  have hc : ((113723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17292378211/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((113723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c174 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((465621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932473/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 138
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t174 : ((44120924551/625000000000 : ℚ) : ℝ) ≤ stT168 174 := by
  have hc : ((116399/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44120924551/625000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((116399/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c175 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((83107/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1474421/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 138
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t175 : ((3926195541/62500000000 : ℚ) : ℝ) ≤ stT168 175 := by
  have hc : ((41551/50000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3926195541/62500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((41551/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c176 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((11881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3867581/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 138
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t176 : ((279274749/156250000000 : ℚ) : ℝ) ≤ stT168 176 := by
  have hc : ((741/31250 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279274749/156250000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((741/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c177 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-800477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6247217/10000000) (δ := 537/62500000) (ψ := 14699/1000000) 168 138
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t177 : ((-601713717969/10000000000000 : ℚ) : ℝ) ≤ stT168 177 := by
  have hc : ((-800527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-601713717969/10000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-800527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c178 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-190843/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7094551/10000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t178 : ((-35762607699/500000000000 : ℚ) : ℝ) ≤ stT168 178 := by
  have hc : ((-190853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35762607699/500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-190853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c179 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-160051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -948317/2000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t179 : ((-7477910321/312500000000 : ℚ) : ℝ) ≤ stT168 179 := by
  have hc : ((-40019/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7477910321/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-40019/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c180 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((572941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -480353/2000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t180 : ((85401434261/2000000000000 : ℚ) : ℝ) ≤ stT168 180 := by
  have hc : ((572891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85401434261/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((572891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c181 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((999551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74881/10000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t181 : ((371461548147/5000000000000 : ℚ) : ℝ) ≤ stT168 181 := by
  have hc : ((999501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((371461548147/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((999501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c182 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((625003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2239151/10000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t182 : ((463245786297/10000000000000 : ℚ) : ℝ) ≤ stT168 182 := by
  have hc : ((624953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((463245786297/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((624953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c183 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-60741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4540541/10000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t183 : ((-44910323777/2500000000000 : ℚ) : ℝ) ≤ stT168 183 := by
  have hc : ((-121507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44910323777/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-121507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c184 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-917183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6829373/10000000) (δ := 1063/125000000) (ψ := 14699/1000000) 168 139
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t184 : ((-67619333993/1000000000000 : ℚ) : ℝ) ≤ stT168 184 := by
  have hc : ((-917233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67619333993/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-917233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c185 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-877231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1650537/2500000) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t185 : ((-128998030083/2000000000000 : ℚ) : ℝ) ≤ stT168 185 := by
  have hc : ((-877281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128998030083/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-877281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c186 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-163669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1084503/2500000) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t186 : ((-30011166171/2500000000000 : ℚ) : ℝ) ≤ stT168 186 := by
  have hc : ((-163719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30011166171/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-163719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c187 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((671631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -521493/2500000) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t187 : ((61388547629/1250000000000 : ℚ) : ℝ) ≤ stT168 187 := by
  have hc : ((671581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61388547629/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((671581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c188 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((998103/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77007/5000000) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t188 : ((181976001543/2500000000000 : ℚ) : ℝ) ≤ stT168 188 := by
  have hc : ((998053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181976001543/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((998053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c189 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((72419/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 595539/2500000) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t189 : ((6584056881/156250000000 : ℚ) : ℝ) ≤ stT168 189 := by
  have hc : ((289651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6584056881/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((289651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c190 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-33173/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143703/312500) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t190 : ((-96283131009/5000000000000 : ℚ) : ℝ) ≤ stT168 190 := by
  have hc : ((-132717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96283131009/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-132717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c191 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-912969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1700811/2500000) (δ := 8407/1000000000) (ψ := 14699/1000000) 168 140
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t191 : ((-26425508917/400000000000 : ℚ) : ℝ) ≤ stT168 191 := by
  have hc : ((-913019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26425508917/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-913019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c192 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-897387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6711521/10000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t192 : ((-80958689207/1250000000000 : ℚ) : ℝ) ≤ stT168 192 := by
  have hc : ((-897437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80958689207/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-897437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c193 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-238757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -905941/2000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t193 : ((-21487137439/1250000000000 : ℚ) : ℝ) ≤ stT168 193 := by
  have hc : ((-238807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21487137439/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-238807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c194 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((58683/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471829/2000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t194 : ((10532084881/250000000000 : ℚ) : ℝ) ≤ stT168 194 := by
  have hc : ((29339/50000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10532084881/250000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((29339/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c195 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((996809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199757/10000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t195 : ((356896537263/5000000000000 : ℚ) : ℝ) ≤ stT168 195 := by
  have hc : ((996759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356896537263/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((996759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c196 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((711311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 389717/2000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t196 : ((101608612677/2000000000000 : ℚ) : ℝ) ≤ stT168 196 := by
  have hc : ((711261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101608612677/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((711261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c197 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-15891/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4086007/10000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t197 : ((-22661565097/5000000000000 : ℚ) : ℝ) ≤ stT168 197 := by
  have hc : ((-31807/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22661565097/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-31807/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c198 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-792099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6212593/10000000) (δ := 4257/500000000) (ψ := 14699/1000000) 168 141
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t198 : ((-56295652983/1000000000000 : ℚ) : ℝ) ≤ stT168 198 := by
  have hc : ((-792149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56295652983/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-792149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c199 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-982043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1475899/2000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t199 : ((-348094025013/5000000000000 : ℚ) : ℝ) ≤ stT168 199 := by
  have hc : ((-982093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348094025013/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-982093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c200 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-256597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1054849/2000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t200 : ((-90729606277/2500000000000 : ℚ) : ℝ) ≤ stT168 200 := by
  have hc : ((-128311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90729606277/2500000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-128311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c201 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((294579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3179453/10000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t201 : ((41548911501/2000000000000 : ℚ) : ℝ) ≤ stT168 201 := by
  have hc : ((294529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41548911501/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((294529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c202 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((452791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1095119/10000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t202 : ((159282399651/2500000000000 : ℚ) : ℝ) ≤ stT168 202 := by
  have hc : ((226383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159282399651/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((226383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c203 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((184861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 978967/10000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t203 : ((64869946281/1000000000000 : ℚ) : ℝ) ≤ stT168 203 := by
  have hc : ((184851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64869946281/1000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((184851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c204 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((346331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3042847/10000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t204 : ((12122258967/500000000000 : ℚ) : ℝ) ≤ stT168 204 := by
  have hc : ((346281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12122258967/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((346281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c205 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-22549/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5096647/10000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t205 : ((-31501333393/1000000000000 : ℚ) : ℝ) ≤ stT168 205 := by
  have hc : ((-45103/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31501333393/1000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-45103/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c206 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-479773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7140451/10000000) (δ := 4291/500000000) (ψ := 14699/1000000) 168 142
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t206 : ((-83572894933/1250000000000 : ℚ) : ℝ) ≤ stT168 206 := by
  have hc : ((-239899/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83572894933/1250000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-239899/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c207 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-13496/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326681/500000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t207 : ((-300189577953/5000000000000 : ℚ) : ℝ) ≤ stT168 207 := by
  have hc : ((-431897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300189577953/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-431897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c208 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-230907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2254757/5000000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t208 : ((-1251094069/78125000000 : ℚ) : ℝ) ≤ stT168 208 := by
  have hc : ((-230957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1251094069/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-230957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c209 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((541947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249511/1000000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t209 : ((187418870729/5000000000000 : ℚ) : ℝ) ≤ stT168 209 := by
  have hc : ((541897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187418870729/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((541897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c210 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((245207/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -122581/2500000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t210 : ((67680057057/1000000000000 : ℚ) : ℝ) ≤ stT168 210 := by
  have hc : ((490389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67680057057/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((490389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c211 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((824221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47029/312500) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t211 : ((141845598297/2500000000000 : ℚ) : ℝ) ≤ stT168 211 := by
  have hc : ((824171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141845598297/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((824171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c212 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((8681/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 349073/1000000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t212 : ((5960411157/500000000000 : ℚ) : ℝ) ≤ stT168 212 := by
  have hc : ((17357/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5960411157/500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((17357/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c213 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-288923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 683401/1250000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t213 : ((-49495997793/1250000000000 : ℚ) : ℝ) ≤ stT168 213 := by
  have hc : ((-72237/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49495997793/1250000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-72237/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c214 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-30811/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3717223/5000000) (δ := 339/40000000) (ψ := 14699/1000000) 168 143
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t214 : ((-168504290793/2500000000000 : ℚ) : ℝ) ≤ stT168 214 := by
  have hc : ((-493001/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168504290793/2500000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-493001/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c215 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-408271/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6315477/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t215 : ((-6961395763/125000000000 : ℚ) : ℝ) ≤ stT168 215 := by
  have hc : ((-51037/62500 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6961395763/125000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-51037/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c216 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-174903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4366509/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t216 : ((-59520235271/5000000000000 : ℚ) : ℝ) ≤ stT168 216 := by
  have hc : ((-174953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59520235271/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-174953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c217 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((564781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2426571/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t217 : ((95841062741/2500000000000 : ℚ) : ℝ) ≤ stT168 217 := by
  have hc : ((564731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95841062741/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((564731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c218 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((49021/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495537/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t218 : ((13279797909/200000000000 : ℚ) : ℝ) ≤ stT168 218 := by
  have hc : ((98037/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13279797909/200000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((98037/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c219 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((841539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1426677/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t219 : ((568625252393/10000000000000 : ℚ) : ℝ) ≤ stT168 219 := by
  have hc : ((841489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568625252393/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((841489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c220 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((232601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3340113/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t220 : ((156785651649/10000000000000 : ℚ) : ℝ) ≤ stT168 220 := by
  have hc : ((232551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156785651649/10000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((232551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c221 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-503083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5244897/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t221 : ((-338443984509/10000000000000 : ℚ) : ℝ) ≤ stT168 221 := by
  have hc : ((-503133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-338443984509/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-503133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c222 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-959611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7141029/10000000) (δ := 1687/200000000) (ψ := 14699/1000000) 168 144
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t222 : ((-644083197777/10000000000000 : ℚ) : ℝ) ≤ stT168 222 := by
  have hc : ((-959661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-644083197777/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-959661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c223 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-891623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3339643/5000000) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t223 : ((-11942176489/200000000000 : ℚ) : ℝ) ≤ stT168 223 := by
  have hc : ((-891673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11942176489/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-891673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c224 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-17109/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60001/125000) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t224 : ((-11433117171/500000000000 : ℚ) : ℝ) ≤ stT168 224 := by
  have hc : ((-34223/100000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11433117171/500000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-34223/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c225 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((24287/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -183077/625000) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t225 : ((64756935243/2500000000000 : ℚ) : ℝ) ≤ stT168 225 := by
  have hc : ((194271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64756935243/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((194271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c226 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((910341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1066721/10000000) (δ := 16943/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t226 : ((60551647029/1000000000000 : ℚ) : ℝ) ≤ stT168 226 := by
  have hc : ((910291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60551647029/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((910291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c227 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((14856/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1969/25000) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t227 : ((315512011341/5000000000000 : ℚ) : ℝ) ≤ stT168 227 := by
  have hc : ((475367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315512011341/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((475367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c228 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((494531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 329219/1250000) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t228 : ((163738976973/5000000000000 : ℚ) : ℝ) ≤ stT168 228 := by
  have hc : ((494481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163738976973/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((494481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c229 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-108109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27949/62500) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t229 : ((-35728500873/2500000000000 : ℚ) : ℝ) ≤ stT168 229 := by
  have hc : ((-54067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35728500873/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-54067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c230 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-203349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3150953/5000000) (δ := 8543/1000000000) (ψ := 14699/1000000) 168 145
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t230 : ((-268185418463/5000000000000 : ℚ) : ℝ) ≤ stT168 230 := by
  have hc : ((-406723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268185418463/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-406723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c231 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-994171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -758393/1000000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t231 : ((-20442177981/312500000000 : ℚ) : ℝ) ≤ stT168 231 := by
  have hc : ((-994221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20442177981/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-994221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c232 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-672131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2884849/5000000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t232 : ((-441309008473/10000000000000 : ℚ) : ℝ) ≤ stT168 232 := by
  have hc : ((-672181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441309008473/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-672181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c233 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-7249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -990809/2500000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t233 : ((-1191339357/1250000000000 : ℚ) : ℝ) ≤ stT168 233 := by
  have hc : ((-3637/250000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1191339357/1250000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-3637/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c234 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((64803/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1082251/5000000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t234 : ((529496857/12500000000 : ℚ) : ℝ) ≤ stT168 234 := by
  have hc : ((32399/50000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529496857/12500000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((32399/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c235 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((988863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186727/5000000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t235 : ((80628800833/1250000000000 : ℚ) : ℝ) ≤ stT168 235 := by
  have hc : ((988813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80628800833/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((988813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c236 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((6761/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176249/1250000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t236 : ((343810313/6250000000 : ℚ) : ℝ) ≤ stT168 236 := by
  have hc : ((33803/40000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((343810313/6250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((33803/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c237 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((146061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1592939/5000000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t237 : ((23715114621/1250000000000 : ℚ) : ℝ) ≤ stT168 237 := by
  have hc : ((36509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23715114621/1250000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((36509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c238 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-99863/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309643/625000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t238 : ((-32369849301/1250000000000 : ℚ) : ℝ) ≤ stT168 238 := by
  have hc : ((-199751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32369849301/1250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-199751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c239 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-449027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3357653/5000000) (δ := 8553/1000000000) (ψ := 14699/1000000) 168 146
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t239 : ((-72616984761/1250000000000 : ℚ) : ℝ) ≤ stT168 239 := by
  have hc : ((-112263/125000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72616984761/1250000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-112263/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c240 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-193979/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7238989/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t240 : ((-62609755761/1000000000000 : ℚ) : ℝ) ≤ stT168 240 := by
  have hc : ((-193989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62609755761/1000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-193989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c241 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-117223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5492629/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t241 : ((-75516457581/2000000000000 : ℚ) : ℝ) ≤ stT168 241 := by
  have hc : ((-117233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75516457581/2000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-117233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c242 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((69343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3753493/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t242 : ((5567900429/1250000000000 : ℚ) : ℝ) ≤ stT168 242 := by
  have hc : ((69293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5567900429/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((69293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c243 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((1381/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2021539/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t243 : ((17716947/400000000 : ℚ) : ℝ) ≤ stT168 243 := by
  have hc : ((13809/20000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17716947/400000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((13809/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c244 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((992967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296683/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t244 : ((79456197091/1250000000000 : ℚ) : ℝ) ≤ stT168 244 := by
  have hc : ((992917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79456197091/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((992917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c245 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((842743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 177637/1250000) (δ := 8423/500000000) (ψ := 14699/1000000) 168 147
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t245 : ((134594083267/2500000000000 : ℚ) : ℝ) ≤ stT168 245 := by
  have hc : ((842693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134594083267/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((842693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c246 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((312701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3131903/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t246 : ((24917346747/1250000000000 : ℚ) : ℝ) ≤ stT168 246 := by
  have hc : ((312651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24917346747/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((312651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c247 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-71111/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4835759/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t247 : ((-9050645097/400000000000 : ℚ) : ℝ) ≤ stT168 247 := by
  have hc : ((-71121/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9050645097/400000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-71121/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c248 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-863563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6532727/10000000) (δ := 4223/500000000) (ψ := 14699/1000000) 168 147
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t248 : ((-548395118613/10000000000000 : ℚ) : ℝ) ≤ stT168 248 := by
  have hc : ((-863613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548395118613/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-863613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c249 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-197827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3742557/5000000) (δ := 529/62500000) (ψ := 14699/1000000) 168 148
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t249 : ((-5014970113/80000000000 : ℚ) : ℝ) ≤ stT168 249 := by
  have hc : ((-197837/200000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5014970113/80000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-197837/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_c250 :
    |Real.cos (((168 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-681557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362607/625000) (δ := 529/62500000) (ψ := 14699/1000000) 168 148
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st168_t250 : ((-53885804599/1250000000000 : ℚ) : ℝ) ≤ stT168 250 := by
  have hc : ((-681607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((168 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st168_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53885804599/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-681607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st168_p1 : ((499921/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT168 (i+1) := by
  rw [Finset.sum_range_one]
  exact st168_t1

theorem st168_p2 : ((765285919407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT168 (i+1))
      = (∑ i ∈ Finset.range 1, stT168 (i+1)) + stT168 2 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 1
    simpa using h
  have hprev := st168_p1
  have hstep := st168_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p3 : ((-954090945249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT168 (i+1))
      = (∑ i ∈ Finset.range 2, stT168 (i+1)) + stT168 3 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 2
    simpa using h
  have hprev := st168_p2
  have hstep := st168_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p4 : ((3641379054751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT168 (i+1))
      = (∑ i ∈ Finset.range 3, stT168 (i+1)) + stT168 4 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 3
    simpa using h
  have hprev := st168_p3
  have hstep := st168_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p5 : ((4014739082983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT168 (i+1))
      = (∑ i ∈ Finset.range 4, stT168 (i+1)) + stT168 5 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 4
    simpa using h
  have hprev := st168_p4
  have hstep := st168_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p6 : ((1427126437819/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT168 (i+1))
      = (∑ i ∈ Finset.range 5, stT168 (i+1)) + stT168 6 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 5
    simpa using h
  have hprev := st168_p5
  have hstep := st168_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p7 : ((757016373401/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT168 (i+1))
      = (∑ i ∈ Finset.range 6, stT168 (i+1)) + stT168 7 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 6
    simpa using h
  have hprev := st168_p6
  have hstep := st168_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p8 : ((382868851909/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT168 (i+1))
      = (∑ i ∈ Finset.range 7, stT168 (i+1)) + stT168 8 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 7
    simpa using h
  have hprev := st168_p7
  have hstep := st168_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p9 : ((11905537027/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT168 (i+1))
      = (∑ i ∈ Finset.range 8, stT168 (i+1)) + stT168 9 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 8
    simpa using h
  have hprev := st168_p8
  have hstep := st168_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p10 : ((4641513597111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT168 (i+1))
      = (∑ i ∈ Finset.range 9, stT168 (i+1)) + stT168 10 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 9
    simpa using h
  have hprev := st168_p9
  have hstep := st168_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p11 : ((1157365678213/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT168 (i+1))
      = (∑ i ∈ Finset.range 10, stT168 (i+1)) + stT168 11 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 10
    simpa using h
  have hprev := st168_p10
  have hstep := st168_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p12 : ((889505403509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT168 (i+1))
      = (∑ i ∈ Finset.range 11, stT168 (i+1)) + stT168 12 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 11
    simpa using h
  have hprev := st168_p11
  have hstep := st168_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p13 : ((3229538506393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT168 (i+1))
      = (∑ i ∈ Finset.range 12, stT168 (i+1)) + stT168 13 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 12
    simpa using h
  have hprev := st168_p12
  have hstep := st168_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p14 : ((397934114777/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT168 (i+1))
      = (∑ i ∈ Finset.range 13, stT168 (i+1)) + stT168 14 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 13
    simpa using h
  have hprev := st168_p13
  have hstep := st168_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p15 : ((1838327467091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT168 (i+1))
      = (∑ i ∈ Finset.range 14, stT168 (i+1)) + stT168 15 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 14
    simpa using h
  have hprev := st168_p14
  have hstep := st168_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p16 : ((3535514967091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT168 (i+1))
      = (∑ i ∈ Finset.range 15, stT168 (i+1)) + stT168 16 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 15
    simpa using h
  have hprev := st168_p15
  have hstep := st168_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p17 : ((3568999432027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT168 (i+1))
      = (∑ i ∈ Finset.range 16, stT168 (i+1)) + stT168 17 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 16
    simpa using h
  have hprev := st168_p16
  have hstep := st168_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p18 : ((3119826272963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT168 (i+1))
      = (∑ i ∈ Finset.range 17, stT168 (i+1)) + stT168 18 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 17
    simpa using h
  have hprev := st168_p17
  have hstep := st168_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p19 : ((2777333719301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT168 (i+1))
      = (∑ i ∈ Finset.range 18, stT168 (i+1)) + stT168 19 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 18
    simpa using h
  have hprev := st168_p18
  have hstep := st168_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p20 : ((2302760986949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT168 (i+1))
      = (∑ i ∈ Finset.range 19, stT168 (i+1)) + stT168 20 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 19
    simpa using h
  have hprev := st168_p19
  have hstep := st168_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p21 : ((2822474423893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT168 (i+1))
      = (∑ i ∈ Finset.range 20, stT168 (i+1)) + stT168 21 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 20
    simpa using h
  have hprev := st168_p20
  have hstep := st168_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p22 : ((1526763617957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT168 (i+1))
      = (∑ i ∈ Finset.range 21, stT168 (i+1)) + stT168 22 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 21
    simpa using h
  have hprev := st168_p21
  have hstep := st168_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p23 : ((2583583406909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT168 (i+1))
      = (∑ i ∈ Finset.range 22, stT168 (i+1)) + stT168 23 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 22
    simpa using h
  have hprev := st168_p22
  have hstep := st168_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p24 : ((2297230473517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT168 (i+1))
      = (∑ i ∈ Finset.range 23, stT168 (i+1)) + stT168 24 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 23
    simpa using h
  have hprev := st168_p23
  have hstep := st168_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p25 : ((3217262473517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT168 (i+1))
      = (∑ i ∈ Finset.range 24, stT168 (i+1)) + stT168 25 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 24
    simpa using h
  have hprev := st168_p24
  have hstep := st168_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p26 : ((1980935099257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT168 (i+1))
      = (∑ i ∈ Finset.range 25, stT168 (i+1)) + stT168 26 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 25
    simpa using h
  have hprev := st168_p25
  have hstep := st168_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p27 : ((581947775533/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT168 (i+1))
      = (∑ i ∈ Finset.range 26, stT168 (i+1)) + stT168 27 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 26
    simpa using h
  have hprev := st168_p26
  have hstep := st168_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p28 : ((679944495343/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT168 (i+1))
      = (∑ i ∈ Finset.range 27, stT168 (i+1)) + stT168 28 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 27
    simpa using h
  have hprev := st168_p27
  have hstep := st168_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p29 : ((3174335935383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT168 (i+1))
      = (∑ i ∈ Finset.range 28, stT168 (i+1)) + stT168 29 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 28
    simpa using h
  have hprev := st168_p28
  have hstep := st168_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p30 : ((14390435529177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT168 (i+1))
      = (∑ i ∈ Finset.range 29, stT168 (i+1)) + stT168 30 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 29
    simpa using h
  have hprev := st168_p29
  have hstep := st168_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p31 : ((15111055098049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT168 (i+1))
      = (∑ i ∈ Finset.range 30, stT168 (i+1)) + stT168 31 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 30
    simpa using h
  have hprev := st168_p30
  have hstep := st168_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p32 : ((14207411498523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT168 (i+1))
      = (∑ i ∈ Finset.range 31, stT168 (i+1)) + stT168 32 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 31
    simpa using h
  have hprev := st168_p31
  have hstep := st168_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p33 : ((3118002939669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT168 (i+1))
      = (∑ i ∈ Finset.range 32, stT168 (i+1)) + stT168 33 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 32
    simpa using h
  have hprev := st168_p32
  have hstep := st168_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p34 : ((3022886386137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT168 (i+1))
      = (∑ i ∈ Finset.range 33, stT168 (i+1)) + stT168 34 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 33
    simpa using h
  have hprev := st168_p33
  have hstep := st168_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p35 : ((3415113905997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT168 (i+1))
      = (∑ i ∈ Finset.range 34, stT168 (i+1)) + stT168 35 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 34
    simpa using h
  have hprev := st168_p34
  have hstep := st168_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p36 : ((178896150377/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT168 (i+1))
      = (∑ i ∈ Finset.range 35, stT168 (i+1)) + stT168 36 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 35
    simpa using h
  have hprev := st168_p35
  have hstep := st168_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p37 : ((1273727404297/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT168 (i+1))
      = (∑ i ∈ Finset.range 36, stT168 (i+1)) + stT168 37 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 36
    simpa using h
  have hprev := st168_p36
  have hstep := st168_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p38 : ((2527982713063/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT168 (i+1))
      = (∑ i ∈ Finset.range 37, stT168 (i+1)) + stT168 38 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 37
    simpa using h
  have hprev := st168_p37
  have hstep := st168_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p39 : ((442966723713/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT168 (i+1))
      = (∑ i ∈ Finset.range 38, stT168 (i+1)) + stT168 39 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 38
    simpa using h
  have hprev := st168_p38
  have hstep := st168_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p40 : ((6549992580277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT168 (i+1))
      = (∑ i ∈ Finset.range 39, stT168 (i+1)) + stT168 40 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 39
    simpa using h
  have hprev := st168_p39
  have hstep := st168_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p41 : ((3174881466083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT168 (i+1))
      = (∑ i ∈ Finset.range 40, stT168 (i+1)) + stT168 41 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 40
    simpa using h
  have hprev := st168_p40
  have hstep := st168_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p42 : ((14117818533579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT168 (i+1))
      = (∑ i ∈ Finset.range 41, stT168 (i+1)) + stT168 42 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 41
    simpa using h
  have hprev := st168_p41
  have hstep := st168_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p43 : ((12717208866753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT168 (i+1))
      = (∑ i ∈ Finset.range 42, stT168 (i+1)) + stT168 43 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 42
    simpa using h
  have hprev := st168_p42
  have hstep := st168_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p44 : ((13363826771161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT168 (i+1))
      = (∑ i ∈ Finset.range 43, stT168 (i+1)) + stT168 44 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 43
    simpa using h
  have hprev := st168_p43
  have hstep := st168_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p45 : ((13646000474929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT168 (i+1))
      = (∑ i ∈ Finset.range 44, stT168 (i+1)) + stT168 45 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 44
    simpa using h
  have hprev := st168_p44
  have hstep := st168_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p46 : ((12650274518649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT168 (i+1))
      = (∑ i ∈ Finset.range 45, stT168 (i+1)) + stT168 46 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 45
    simpa using h
  have hprev := st168_p45
  have hstep := st168_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p47 : ((14016380991493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT168 (i+1))
      = (∑ i ∈ Finset.range 46, stT168 (i+1)) + stT168 47 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 46
    simpa using h
  have hprev := st168_p46
  have hstep := st168_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p48 : ((12573941742517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT168 (i+1))
      = (∑ i ∈ Finset.range 47, stT168 (i+1)) + stT168 48 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 47
    simpa using h
  have hprev := st168_p47
  have hstep := st168_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p49 : ((13910949912843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT168 (i+1))
      = (∑ i ∈ Finset.range 48, stT168 (i+1)) + stT168 49 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 48
    simpa using h
  have hprev := st168_p48
  have hstep := st168_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p50 : ((12753595359021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT168 (i+1))
      = (∑ i ∈ Finset.range 49, stT168 (i+1)) + stT168 50 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 49
    simpa using h
  have hprev := st168_p49
  have hstep := st168_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p51 : ((13731564913821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT168 (i+1))
      = (∑ i ∈ Finset.range 50, stT168 (i+1)) + stT168 51 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 50
    simpa using h
  have hprev := st168_p50
  have hstep := st168_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p52 : ((12889391031521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT168 (i+1))
      = (∑ i ∈ Finset.range 51, stT168 (i+1)) + stT168 52 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 51
    simpa using h
  have hprev := st168_p51
  have hstep := st168_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p53 : ((6829102309023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT168 (i+1))
      = (∑ i ∈ Finset.range 52, stT168 (i+1)) + stT168 53 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 52
    simpa using h
  have hprev := st168_p52
  have hstep := st168_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p54 : ((6447459457251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT168 (i+1))
      = (∑ i ∈ Finset.range 53, stT168 (i+1)) + stT168 54 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 53
    simpa using h
  have hprev := st168_p53
  have hstep := st168_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p55 : ((2743110100141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT168 (i+1))
      = (∑ i ∈ Finset.range 54, stT168 (i+1)) + stT168 55 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 54
    simpa using h
  have hprev := st168_p54
  have hstep := st168_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p56 : ((3196587022987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT168 (i+1))
      = (∑ i ∈ Finset.range 55, stT168 (i+1)) + stT168 56 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 55
    simpa using h
  have hprev := st168_p55
  have hstep := st168_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p57 : ((1731686301381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT168 (i+1))
      = (∑ i ∈ Finset.range 56, stT168 (i+1)) + stT168 57 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 56
    simpa using h
  have hprev := st168_p56
  have hstep := st168_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p58 : ((6325677884189/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT168 (i+1))
      = (∑ i ∈ Finset.range 57, stT168 (i+1)) + stT168 58 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 57
    simpa using h
  have hprev := st168_p57
  have hstep := st168_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p59 : ((2787926183021/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT168 (i+1))
      = (∑ i ∈ Finset.range 58, stT168 (i+1)) + stT168 59 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 58
    simpa using h
  have hprev := st168_p58
  have hstep := st168_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p60 : ((2533595520439/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT168 (i+1))
      = (∑ i ∈ Finset.range 59, stT168 (i+1)) + stT168 60 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 59
    simpa using h
  have hprev := st168_p59
  have hstep := st168_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p61 : ((13767229866387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT168 (i+1))
      = (∑ i ∈ Finset.range 60, stT168 (i+1)) + stT168 61 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 60
    simpa using h
  have hprev := st168_p60
  have hstep := st168_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p62 : ((13026470719839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT168 (i+1))
      = (∑ i ∈ Finset.range 61, stT168 (i+1)) + stT168 62 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 61
    simpa using h
  have hprev := st168_p61
  have hstep := st168_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p63 : ((1323852255083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT168 (i+1))
      = (∑ i ∈ Finset.range 62, stT168 (i+1)) + stT168 63 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 62
    simpa using h
  have hprev := st168_p62
  have hstep := st168_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p64 : ((1363962380083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT168 (i+1))
      = (∑ i ∈ Finset.range 63, stT168 (i+1)) + stT168 64 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 63
    simpa using h
  have hprev := st168_p63
  have hstep := st168_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p65 : ((6348333299351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT168 (i+1))
      = (∑ i ∈ Finset.range 64, stT168 (i+1)) + stT168 65 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 64
    simpa using h
  have hprev := st168_p64
  have hstep := st168_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p66 : ((869815325361/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT168 (i+1))
      = (∑ i ∈ Finset.range 65, stT168 (i+1)) + stT168 66 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 65
    simpa using h
  have hprev := st168_p65
  have hstep := st168_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p67 : ((6417999532173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT168 (i+1))
      = (∑ i ∈ Finset.range 66, stT168 (i+1)) + stT168 67 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 66
    simpa using h
  have hprev := st168_p66
  have hstep := st168_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p68 : ((667263947763/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT168 (i+1))
      = (∑ i ∈ Finset.range 67, stT168 (i+1)) + stT168 68 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 67
    simpa using h
  have hprev := st168_p67
  have hstep := st168_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p69 : ((6824754761007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT168 (i+1))
      = (∑ i ∈ Finset.range 68, stT168 (i+1)) + stT168 69 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 68
    simpa using h
  have hprev := st168_p68
  have hstep := st168_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p70 : ((3164232899741/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT168 (i+1))
      = (∑ i ∈ Finset.range 69, stT168 (i+1)) + stT168 70 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 69
    simpa using h
  have hprev := st168_p69
  have hstep := st168_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p71 : ((691351085549/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT168 (i+1))
      = (∑ i ∈ Finset.range 70, stT168 (i+1)) + stT168 71 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 70
    simpa using h
  have hprev := st168_p70
  have hstep := st168_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p72 : ((3287645732189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT168 (i+1))
      = (∑ i ∈ Finset.range 71, stT168 (i+1)) + stT168 72 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 71
    simpa using h
  have hprev := st168_p71
  have hstep := st168_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p73 : ((645153912197/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT168 (i+1))
      = (∑ i ∈ Finset.range 72, stT168 (i+1)) + stT168 73 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 72
    simpa using h
  have hprev := st168_p72
  have hstep := st168_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p74 : ((1740264686597/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT168 (i+1))
      = (∑ i ∈ Finset.range 73, stT168 (i+1)) + stT168 74 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 73
    simpa using h
  have hprev := st168_p73
  have hstep := st168_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p75 : ((514068340443/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT168 (i+1))
      = (∑ i ∈ Finset.range 74, stT168 (i+1)) + stT168 75 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 74
    simpa using h
  have hprev := st168_p74
  have hstep := st168_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p76 : ((13157396768529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT168 (i+1))
      = (∑ i ∈ Finset.range 75, stT168 (i+1)) + stT168 76 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 75
    simpa using h
  have hprev := st168_p75
  have hstep := st168_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p77 : ((3467519311351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT168 (i+1))
      = (∑ i ∈ Finset.range 76, stT168 (i+1)) + stT168 77 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 76
    simpa using h
  have hprev := st168_p76
  have hstep := st168_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p78 : ((6370623515957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT168 (i+1))
      = (∑ i ∈ Finset.range 77, stT168 (i+1)) + stT168 78 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 77
    simpa using h
  have hprev := st168_p77
  have hstep := st168_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p79 : ((1658917034039/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT168 (i+1))
      = (∑ i ∈ Finset.range 78, stT168 (i+1)) + stT168 79 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 78
    simpa using h
  have hprev := st168_p78
  have hstep := st168_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p80 : ((553755730799/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT168 (i+1))
      = (∑ i ∈ Finset.range 79, stT168 (i+1)) + stT168 80 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 79
    simpa using h
  have hprev := st168_p79
  have hstep := st168_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p81 : ((12732982381247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT168 (i+1))
      = (∑ i ∈ Finset.range 80, stT168 (i+1)) + stT168 81 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 80
    simpa using h
  have hprev := st168_p80
  have hstep := st168_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p82 : ((827008504637/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT168 (i+1))
      = (∑ i ∈ Finset.range 81, stT168 (i+1)) + stT168 82 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 81
    simpa using h
  have hprev := st168_p81
  have hstep := st168_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p83 : ((1388417823023/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT168 (i+1))
      = (∑ i ∈ Finset.range 82, stT168 (i+1)) + stT168 83 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 82
    simpa using h
  have hprev := st168_p82
  have hstep := st168_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p84 : ((1281369892033/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT168 (i+1))
      = (∑ i ∈ Finset.range 83, stT168 (i+1)) + stT168 84 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 83
    simpa using h
  have hprev := st168_p83
  have hstep := st168_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p85 : ((6526473559941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT168 (i+1))
      = (∑ i ∈ Finset.range 84, stT168 (i+1)) + stT168 85 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 84
    simpa using h
  have hprev := st168_p84
  have hstep := st168_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p86 : ((3483163189111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT168 (i+1))
      = (∑ i ∈ Finset.range 85, stT168 (i+1)) + stT168 86 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 85
    simpa using h
  have hprev := st168_p85
  have hstep := st168_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p87 : ((13037450194687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT168 (i+1))
      = (∑ i ∈ Finset.range 86, stT168 (i+1)) + stT168 87 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 86
    simpa using h
  have hprev := st168_p86
  have hstep := st168_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p88 : ((12790690522763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT168 (i+1))
      = (∑ i ∈ Finset.range 87, stT168 (i+1)) + stT168 88 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 87
    simpa using h
  have hprev := st168_p87
  have hstep := st168_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p89 : ((13845957816149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT168 (i+1))
      = (∑ i ∈ Finset.range 88, stT168 (i+1)) + stT168 89 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 88
    simpa using h
  have hprev := st168_p88
  have hstep := st168_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p90 : ((13435141934887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT168 (i+1))
      = (∑ i ∈ Finset.range 89, stT168 (i+1)) + stT168 90 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 89
    simpa using h
  have hprev := st168_p89
  have hstep := st168_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p91 : ((12623853207687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT168 (i+1))
      = (∑ i ∈ Finset.range 90, stT168 (i+1)) + stT168 91 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 90
    simpa using h
  have hprev := st168_p90
  have hstep := st168_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p92 : ((13472543305707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT168 (i+1))
      = (∑ i ∈ Finset.range 91, stT168 (i+1)) + stT168 92 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 91
    simpa using h
  have hprev := st168_p91
  have hstep := st168_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p93 : ((3462883853961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT168 (i+1))
      = (∑ i ∈ Finset.range 92, stT168 (i+1)) + stT168 93 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 92
    simpa using h
  have hprev := st168_p92
  have hstep := st168_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p94 : ((6415683630643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT168 (i+1))
      = (∑ i ∈ Finset.range 93, stT168 (i+1)) + stT168 94 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 93
    simpa using h
  have hprev := st168_p93
  have hstep := st168_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p95 : ((1611451201439/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT168 (i+1))
      = (∑ i ∈ Finset.range 94, stT168 (i+1)) + stT168 95 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 94
    simpa using h
  have hprev := st168_p94
  have hstep := st168_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p96 : ((1735144732029/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT168 (i+1))
      = (∑ i ∈ Finset.range 95, stT168 (i+1)) + stT168 96 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 95
    simpa using h
  have hprev := st168_p95
  have hstep := st168_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p97 : ((13469559535413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT168 (i+1))
      = (∑ i ∈ Finset.range 96, stT168 (i+1)) + stT168 97 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 96
    simpa using h
  have hprev := st168_p96
  have hstep := st168_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p98 : ((1577357524577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT168 (i+1))
      = (∑ i ∈ Finset.range 97, stT168 (i+1)) + stT168 98 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 97
    simpa using h
  have hprev := st168_p97
  have hstep := st168_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p99 : ((530787157649/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT168 (i+1))
      = (∑ i ∈ Finset.range 98, stT168 (i+1)) + stT168 99 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 98
    simpa using h
  have hprev := st168_p98
  have hstep := st168_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p100 : ((6975158630293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT168 (i+1))
      = (∑ i ∈ Finset.range 99, stT168 (i+1)) + stT168 100 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 99
    simpa using h
  have hprev := st168_p99
  have hstep := st168_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p101 : ((6578415088857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT168 (i+1))
      = (∑ i ∈ Finset.range 100, stT168 (i+1)) + stT168 101 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 100
    simpa using h
  have hprev := st168_p100
  have hstep := st168_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p102 : ((6313971806831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT168 (i+1))
      = (∑ i ∈ Finset.range 101, stT168 (i+1)) + stT168 102 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 101
    simpa using h
  have hprev := st168_p101
  have hstep := st168_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p103 : ((2698970563691/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT168 (i+1))
      = (∑ i ∈ Finset.range 102, stT168 (i+1)) + stT168 103 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 102
    simpa using h
  have hprev := st168_p102
  have hstep := st168_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p104 : ((2782992737687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT168 (i+1))
      = (∑ i ∈ Finset.range 103, stT168 (i+1)) + stT168 104 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 103
    simpa using h
  have hprev := st168_p103
  have hstep := st168_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p105 : ((260366409763/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT168 (i+1))
      = (∑ i ∈ Finset.range 104, stT168 (i+1)) + stT168 105 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 104
    simpa using h
  have hprev := st168_p104
  have hstep := st168_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p106 : ((6327060630937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT168 (i+1))
      = (∑ i ∈ Finset.range 105, stT168 (i+1)) + stT168 106 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 105
    simpa using h
  have hprev := st168_p105
  have hstep := st168_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p107 : ((1355269850693/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT168 (i+1))
      = (∑ i ∈ Finset.range 106, stT168 (i+1)) + stT168 107 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 106
    simpa using h
  have hprev := st168_p106
  have hstep := st168_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p108 : ((695728737559/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT168 (i+1))
      = (∑ i ∈ Finset.range 107, stT168 (i+1)) + stT168 108 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 107
    simpa using h
  have hprev := st168_p107
  have hstep := st168_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p109 : ((651766393913/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT168 (i+1))
      = (∑ i ∈ Finset.range 108, stT168 (i+1)) + stT168 109 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 108
    simpa using h
  have hprev := st168_p108
  have hstep := st168_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p110 : ((3156309907027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT168 (i+1))
      = (∑ i ∈ Finset.range 109, stT168 (i+1)) + stT168 110 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 109
    simpa using h
  have hprev := st168_p109
  have hstep := st168_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p111 : ((13460436092903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT168 (i+1))
      = (∑ i ∈ Finset.range 110, stT168 (i+1)) + stT168 111 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 110
    simpa using h
  have hprev := st168_p110
  have hstep := st168_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p112 : ((13961541294423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT168 (i+1))
      = (∑ i ∈ Finset.range 111, stT168 (i+1)) + stT168 112 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 111
    simpa using h
  have hprev := st168_p111
  have hstep := st168_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p113 : ((13204973955941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT168 (i+1))
      = (∑ i ∈ Finset.range 112, stT168 (i+1)) + stT168 113 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 112
    simpa using h
  have hprev := st168_p112
  have hstep := st168_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p114 : ((12582374666097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT168 (i+1))
      = (∑ i ∈ Finset.range 113, stT168 (i+1)) + stT168 114 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 113
    simpa using h
  have hprev := st168_p113
  have hstep := st168_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p115 : ((13211217131033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT168 (i+1))
      = (∑ i ∈ Finset.range 114, stT168 (i+1)) + stT168 115 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 114
    simpa using h
  have hprev := st168_p114
  have hstep := st168_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p116 : ((13964720900357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT168 (i+1))
      = (∑ i ∈ Finset.range 115, stT168 (i+1)) + stT168 116 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 115
    simpa using h
  have hprev := st168_p115
  have hstep := st168_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p117 : ((2705069990221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT168 (i+1))
      = (∑ i ∈ Finset.range 116, stT168 (i+1)) + stT168 117 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 116
    simpa using h
  have hprev := st168_p116
  have hstep := st168_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p118 : ((2532374538981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT168 (i+1))
      = (∑ i ∈ Finset.range 117, stT168 (i+1)) + stT168 118 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 117
    simpa using h
  have hprev := st168_p117
  have hstep := st168_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p119 : ((12844950119277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT168 (i+1))
      = (∑ i ∈ Finset.range 118, stT168 (i+1)) + stT168 119 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 118
    simpa using h
  have hprev := st168_p118
  have hstep := st168_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p120 : ((13757176545927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT168 (i+1))
      = (∑ i ∈ Finset.range 119, stT168 (i+1)) + stT168 120 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 119
    simpa using h
  have hprev := st168_p119
  have hstep := st168_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p121 : ((13884350055117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT168 (i+1))
      = (∑ i ∈ Finset.range 120, stT168 (i+1)) + stT168 121 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 120
    simpa using h
  have hprev := st168_p120
  have hstep := st168_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p122 : ((13027350847329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT168 (i+1))
      = (∑ i ∈ Finset.range 121, stT168 (i+1)) + stT168 122 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 121
    simpa using h
  have hprev := st168_p121
  have hstep := st168_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p123 : ((12573166143279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT168 (i+1))
      = (∑ i ∈ Finset.range 122, stT168 (i+1)) + stT168 123 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 122
    simpa using h
  have hprev := st168_p122
  have hstep := st168_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p124 : ((13237312047891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT168 (i+1))
      = (∑ i ∈ Finset.range 123, stT168 (i+1)) + stT168 124 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 123
    simpa using h
  have hprev := st168_p123
  have hstep := st168_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p125 : ((13969815561519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT168 (i+1))
      = (∑ i ∈ Finset.range 124, stT168 (i+1)) + stT168 125 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 124
    simpa using h
  have hprev := st168_p124
  have hstep := st168_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p126 : ((13640182601067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT168 (i+1))
      = (∑ i ∈ Finset.range 125, stT168 (i+1)) + stT168 126 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 125
    simpa using h
  have hprev := st168_p125
  have hstep := st168_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p127 : ((6380501297911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT168 (i+1))
      = (∑ i ∈ Finset.range 126, stT168 (i+1)) + stT168 127 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 126
    simpa using h
  have hprev := st168_p126
  have hstep := st168_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p128 : ((6328929318163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT168 (i+1))
      = (∑ i ∈ Finset.range 127, stT168 (i+1)) + stT168 128 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 127
    simpa using h
  have hprev := st168_p127
  have hstep := st168_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p129 : ((6737679991563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT168 (i+1))
      = (∑ i ∈ Finset.range 128, stT168 (i+1)) + stT168 129 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 128
    simpa using h
  have hprev := st168_p128
  have hstep := st168_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p130 : ((3502186797779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT168 (i+1))
      = (∑ i ∈ Finset.range 129, stT168 (i+1)) + stT168 130 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 129
    simpa using h
  have hprev := st168_p129
  have hstep := st168_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p131 : ((13491448303241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT168 (i+1))
      = (∑ i ∈ Finset.range 130, stT168 (i+1)) + stT168 131 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 130
    simpa using h
  have hprev := st168_p130
  have hstep := st168_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p132 : ((633547108361/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT168 (i+1))
      = (∑ i ∈ Finset.range 131, stT168 (i+1)) + stT168 132 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 131
    simpa using h
  have hprev := st168_p131
  have hstep := st168_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p133 : ((6351694693/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT168 (i+1))
      = (∑ i ∈ Finset.range 132, stT168 (i+1)) + stT168 133 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 132
    simpa using h
  have hprev := st168_p132
  have hstep := st168_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p134 : ((1691847641551/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT168 (i+1))
      = (∑ i ∈ Finset.range 133, stT168 (i+1)) + stT168 134 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 133
    simpa using h
  have hprev := st168_p133
  have hstep := st168_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p135 : ((3504573970009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT168 (i+1))
      = (∑ i ∈ Finset.range 134, stT168 (i+1)) + stT168 135 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 134
    simpa using h
  have hprev := st168_p134
  have hstep := st168_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p136 : ((843995865559/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT168 (i+1))
      = (∑ i ∈ Finset.range 135, stT168 (i+1)) + stT168 136 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 135
    simpa using h
  have hprev := st168_p135
  have hstep := st168_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p137 : ((3172128090109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT168 (i+1))
      = (∑ i ∈ Finset.range 136, stT168 (i+1)) + stT168 137 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 136
    simpa using h
  have hprev := st168_p136
  have hstep := st168_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p138 : ((3162384602487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT168 (i+1))
      = (∑ i ∈ Finset.range 137, stT168 (i+1)) + stT168 138 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 137
    simpa using h
  have hprev := st168_p137
  have hstep := st168_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p139 : ((3357388961003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT168 (i+1))
      = (∑ i ∈ Finset.range 138, stT168 (i+1)) + stT168 139 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 138
    simpa using h
  have hprev := st168_p138
  have hstep := st168_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p140 : ((7008935039437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT168 (i+1))
      = (∑ i ∈ Finset.range 139, stT168 (i+1)) + stT168 140 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 139
    simpa using h
  have hprev := st168_p139
  have hstep := st168_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p141 : ((1367005540781/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT168 (i+1))
      = (∑ i ∈ Finset.range 140, stT168 (i+1)) + stT168 141 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 140
    simpa using h
  have hprev := st168_p140
  have hstep := st168_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p142 : ((1283157832069/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT168 (i+1))
      = (∑ i ∈ Finset.range 141, stT168 (i+1)) + stT168 142 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 141
    simpa using h
  have hprev := st168_p141
  have hstep := st168_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p143 : ((6272534044501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT168 (i+1))
      = (∑ i ∈ Finset.range 142, stT168 (i+1)) + stT168 143 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 142
    simpa using h
  have hprev := st168_p142
  have hstep := st168_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p144 : ((526197080469/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT168 (i+1))
      = (∑ i ∈ Finset.range 143, stT168 (i+1)) + stT168 144 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 143
    simpa using h
  have hprev := st168_p143
  have hstep := st168_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p145 : ((13915540660779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT168 (i+1))
      = (∑ i ∈ Finset.range 144, stT168 (i+1)) + stT168 145 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 144
    simpa using h
  have hprev := st168_p144
  have hstep := st168_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p146 : ((13918167479049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT168 (i+1))
      = (∑ i ∈ Finset.range 145, stT168 (i+1)) + stT168 146 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 145
    simpa using h
  have hprev := st168_p145
  have hstep := st168_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p147 : ((3291871691553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT168 (i+1))
      = (∑ i ∈ Finset.range 146, stT168 (i+1)) + stT168 147 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 146
    simpa using h
  have hprev := st168_p146
  have hstep := st168_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p148 : ((12544998994657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT168 (i+1))
      = (∑ i ∈ Finset.range 147, stT168 (i+1)) + stT168 148 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 147
    simpa using h
  have hprev := st168_p147
  have hstep := st168_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p149 : ((12765250887469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT168 (i+1))
      = (∑ i ∈ Finset.range 148, stT168 (i+1)) + stT168 149 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 148
    simpa using h
  have hprev := st168_p148
  have hstep := st168_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p150 : ((13569262663629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT168 (i+1))
      = (∑ i ∈ Finset.range 149, stT168 (i+1)) + stT168 150 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 149
    simpa using h
  have hprev := st168_p149
  have hstep := st168_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p151 : ((14048207825573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT168 (i+1))
      = (∑ i ∈ Finset.range 150, stT168 (i+1)) + stT168 151 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 150
    simpa using h
  have hprev := st168_p150
  have hstep := st168_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p152 : ((13673897705733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT168 (i+1))
      = (∑ i ∈ Finset.range 151, stT168 (i+1)) + stT168 152 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 151
    simpa using h
  have hprev := st168_p151
  have hstep := st168_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p153 : ((6432724373999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT168 (i+1))
      = (∑ i ∈ Finset.range 152, stT168 (i+1)) + stT168 153 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 152
    simpa using h
  have hprev := st168_p152
  have hstep := st168_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p154 : ((3125857385489/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT168 (i+1))
      = (∑ i ∈ Finset.range 153, stT168 (i+1)) + stT168 154 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 153
    simpa using h
  have hprev := st168_p153
  have hstep := st168_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p155 : ((6485535837973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT168 (i+1))
      = (∑ i ∈ Finset.range 154, stT168 (i+1)) + stT168 155 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 154
    simpa using h
  have hprev := st168_p154
  have hstep := st168_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p156 : ((6882400676053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT168 (i+1))
      = (∑ i ∈ Finset.range 155, stT168 (i+1)) + stT168 156 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 155
    simpa using h
  have hprev := st168_p155
  have hstep := st168_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p157 : ((70252696423/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT168 (i+1))
      = (∑ i ∈ Finset.range 156, stT168 (i+1)) + stT168 157 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 156
    simpa using h
  have hprev := st168_p156
  have hstep := st168_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p158 : ((6768854536657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT168 (i+1))
      = (∑ i ∈ Finset.range 157, stT168 (i+1)) + stT168 158 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 157
    simpa using h
  have hprev := st168_p157
  have hstep := st168_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p159 : ((6379414852803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT168 (i+1))
      = (∑ i ∈ Finset.range 158, stT168 (i+1)) + stT168 159 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 158
    simpa using h
  have hprev := st168_p158
  have hstep := st168_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p160 : ((97688943257/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT168 (i+1))
      = (∑ i ∈ Finset.range 159, stT168 (i+1)) + stT168 160 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 159
    simpa using h
  have hprev := st168_p159
  have hstep := st168_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p161 : ((1627889667827/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT168 (i+1))
      = (∑ i ∈ Finset.range 160, stT168 (i+1)) + stT168 161 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 160
    simpa using h
  have hprev := st168_p160
  have hstep := st168_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p162 : ((43108956427/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT168 (i+1))
      = (∑ i ∈ Finset.range 161, stT168 (i+1)) + stT168 162 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 161
    simpa using h
  have hprev := st168_p161
  have hstep := st168_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p163 : ((21972523657/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT168 (i+1))
      = (∑ i ∈ Finset.range 162, stT168 (i+1)) + stT168 163 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 162
    simpa using h
  have hprev := st168_p162
  have hstep := st168_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p164 : ((13572059862371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT168 (i+1))
      = (∑ i ∈ Finset.range 163, stT168 (i+1)) + stT168 164 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 163
    simpa using h
  have hprev := st168_p163
  have hstep := st168_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p165 : ((800001546223/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT168 (i+1))
      = (∑ i ∈ Finset.range 164, stT168 (i+1)) + stT168 165 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 164
    simpa using h
  have hprev := st168_p164
  have hstep := st168_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p166 : ((1247901023827/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT168 (i+1))
      = (∑ i ∈ Finset.range 165, stT168 (i+1)) + stT168 166 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 165
    simpa using h
  have hprev := st168_p165
  have hstep := st168_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p167 : ((12904776164923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT168 (i+1))
      = (∑ i ∈ Finset.range 166, stT168 (i+1)) + stT168 167 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 166
    simpa using h
  have hprev := st168_p166
  have hstep := st168_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p168 : ((13676168722363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT168 (i+1))
      = (∑ i ∈ Finset.range 167, stT168 (i+1)) + stT168 168 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 167
    simpa using h
  have hprev := st168_p167
  have hstep := st168_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p169 : ((14084012160673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT168 (i+1))
      = (∑ i ∈ Finset.range 168, stT168 (i+1)) + stT168 169 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 168
    simpa using h
  have hprev := st168_p168
  have hstep := st168_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p170 : ((13762675300693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT168 (i+1))
      = (∑ i ∈ Finset.range 169, stT168 (i+1)) + stT168 170 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 169
    simpa using h
  have hprev := st168_p169
  have hstep := st168_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p171 : ((13006874230053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT168 (i+1))
      = (∑ i ∈ Finset.range 170, stT168 (i+1)) + stT168 171 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 170
    simpa using h
  have hprev := st168_p170
  have hstep := st168_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p172 : ((2498043929631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT168 (i+1))
      = (∑ i ∈ Finset.range 171, stT168 (i+1)) + stT168 172 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 171
    simpa using h
  have hprev := st168_p171
  have hstep := st168_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p173 : ((2532628686053/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT168 (i+1))
      = (∑ i ∈ Finset.range 172, stT168 (i+1)) + stT168 173 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 172
    simpa using h
  have hprev := st168_p172
  have hstep := st168_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p174 : ((13369078223081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT168 (i+1))
      = (∑ i ∈ Finset.range 173, stT168 (i+1)) + stT168 174 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 173
    simpa using h
  have hprev := st168_p173
  have hstep := st168_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p175 : ((13997269509641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT168 (i+1))
      = (∑ i ∈ Finset.range 174, stT168 (i+1)) + stT168 175 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 174
    simpa using h
  have hprev := st168_p174
  have hstep := st168_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p176 : ((14015143093577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT168 (i+1))
      = (∑ i ∈ Finset.range 175, stT168 (i+1)) + stT168 176 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 175
    simpa using h
  have hprev := st168_p175
  have hstep := st168_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p177 : ((1676678671951/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT168 (i+1))
      = (∑ i ∈ Finset.range 176, stT168 (i+1)) + stT168 177 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 176
    simpa using h
  have hprev := st168_p176
  have hstep := st168_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p178 : ((3174544305407/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT168 (i+1))
      = (∑ i ∈ Finset.range 177, stT168 (i+1)) + stT168 178 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 177
    simpa using h
  have hprev := st168_p177
  have hstep := st168_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p179 : ((3114721022839/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT168 (i+1))
      = (∑ i ∈ Finset.range 178, stT168 (i+1)) + stT168 179 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 178
    simpa using h
  have hprev := st168_p178
  have hstep := st168_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p180 : ((12885891262661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT168 (i+1))
      = (∑ i ∈ Finset.range 179, stT168 (i+1)) + stT168 180 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 179
    simpa using h
  have hprev := st168_p179
  have hstep := st168_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p181 : ((2725762871791/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT168 (i+1))
      = (∑ i ∈ Finset.range 180, stT168 (i+1)) + stT168 181 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 180
    simpa using h
  have hprev := st168_p180
  have hstep := st168_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p182 : ((3523015036313/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT168 (i+1))
      = (∑ i ∈ Finset.range 181, stT168 (i+1)) + stT168 182 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 181
    simpa using h
  have hprev := st168_p181
  have hstep := st168_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p183 : ((434763089067/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT168 (i+1))
      = (∑ i ∈ Finset.range 182, stT168 (i+1)) + stT168 183 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 182
    simpa using h
  have hprev := st168_p182
  have hstep := st168_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p184 : ((6618112755107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT168 (i+1))
      = (∑ i ∈ Finset.range 183, stT168 (i+1)) + stT168 184 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 183
    simpa using h
  have hprev := st168_p183
  have hstep := st168_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p185 : ((12591235359799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT168 (i+1))
      = (∑ i ∈ Finset.range 184, stT168 (i+1)) + stT168 185 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 184
    simpa using h
  have hprev := st168_p184
  have hstep := st168_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p186 : ((2494238139023/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT168 (i+1))
      = (∑ i ∈ Finset.range 185, stT168 (i+1)) + stT168 186 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 185
    simpa using h
  have hprev := st168_p185
  have hstep := st168_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p187 : ((12962299076147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT168 (i+1))
      = (∑ i ∈ Finset.range 186, stT168 (i+1)) + stT168 187 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 186
    simpa using h
  have hprev := st168_p186
  have hstep := st168_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p188 : ((13690203082319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT168 (i+1))
      = (∑ i ∈ Finset.range 187, stT168 (i+1)) + stT168 188 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 187
    simpa using h
  have hprev := st168_p187
  have hstep := st168_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p189 : ((14111582722703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT168 (i+1))
      = (∑ i ∈ Finset.range 188, stT168 (i+1)) + stT168 189 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 188
    simpa using h
  have hprev := st168_p188
  have hstep := st168_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p190 : ((2783803292137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT168 (i+1))
      = (∑ i ∈ Finset.range 189, stT168 (i+1)) + stT168 190 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 189
    simpa using h
  have hprev := st168_p189
  have hstep := st168_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p191 : ((82864867111/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT168 (i+1))
      = (∑ i ∈ Finset.range 190, stT168 (i+1)) + stT168 191 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 190
    simpa using h
  have hprev := st168_p190
  have hstep := st168_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p192 : ((1576338653013/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT168 (i+1))
      = (∑ i ∈ Finset.range 191, stT168 (i+1)) + stT168 192 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 191
    simpa using h
  have hprev := st168_p191
  have hstep := st168_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p193 : ((777425757787/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT168 (i+1))
      = (∑ i ∈ Finset.range 192, stT168 (i+1)) + stT168 193 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 192
    simpa using h
  have hprev := st168_p192
  have hstep := st168_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p194 : ((1607511939979/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT168 (i+1))
      = (∑ i ∈ Finset.range 193, stT168 (i+1)) + stT168 194 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 193
    simpa using h
  have hprev := st168_p193
  have hstep := st168_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p195 : ((6786944297179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT168 (i+1))
      = (∑ i ∈ Finset.range 194, stT168 (i+1)) + stT168 195 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 194
    simpa using h
  have hprev := st168_p194
  have hstep := st168_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p196 : ((14081931657743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT168 (i+1))
      = (∑ i ∈ Finset.range 195, stT168 (i+1)) + stT168 196 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 195
    simpa using h
  have hprev := st168_p195
  have hstep := st168_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p197 : ((14036608527549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT168 (i+1))
      = (∑ i ∈ Finset.range 196, stT168 (i+1)) + stT168 197 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 196
    simpa using h
  have hprev := st168_p196
  have hstep := st168_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p198 : ((13473651997719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT168 (i+1))
      = (∑ i ∈ Finset.range 197, stT168 (i+1)) + stT168 198 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 197
    simpa using h
  have hprev := st168_p197
  have hstep := st168_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p199 : ((12777463947693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT168 (i+1))
      = (∑ i ∈ Finset.range 198, stT168 (i+1)) + stT168 199 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 198
    simpa using h
  have hprev := st168_p198
  have hstep := st168_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p200 : ((2482909104517/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT168 (i+1))
      = (∑ i ∈ Finset.range 199, stT168 (i+1)) + stT168 200 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 199
    simpa using h
  have hprev := st168_p199
  have hstep := st168_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p201 : ((1262229008009/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT168 (i+1))
      = (∑ i ∈ Finset.range 200, stT168 (i+1)) + stT168 201 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 200
    simpa using h
  have hprev := st168_p200
  have hstep := st168_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p202 : ((6629709839347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT168 (i+1))
      = (∑ i ∈ Finset.range 201, stT168 (i+1)) + stT168 202 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 201
    simpa using h
  have hprev := st168_p201
  have hstep := st168_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p203 : ((108657180793/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT168 (i+1))
      = (∑ i ∈ Finset.range 202, stT168 (i+1)) + stT168 203 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 202
    simpa using h
  have hprev := st168_p202
  have hstep := st168_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p204 : ((3537641080211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT168 (i+1))
      = (∑ i ∈ Finset.range 203, stT168 (i+1)) + stT168 204 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 203
    simpa using h
  have hprev := st168_p203
  have hstep := st168_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p205 : ((6917775493457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT168 (i+1))
      = (∑ i ∈ Finset.range 204, stT168 (i+1)) + stT168 205 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 204
    simpa using h
  have hprev := st168_p204
  have hstep := st168_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p206 : ((263339356549/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT168 (i+1))
      = (∑ i ∈ Finset.range 205, stT168 (i+1)) + stT168 206 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 205
    simpa using h
  have hprev := st168_p205
  have hstep := st168_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p207 : ((1570823583943/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT168 (i+1))
      = (∑ i ∈ Finset.range 206, stT168 (i+1)) + stT168 207 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 206
    simpa using h
  have hprev := st168_p206
  have hstep := st168_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p208 : ((1550806078839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT168 (i+1))
      = (∑ i ∈ Finset.range 207, stT168 (i+1)) + stT168 208 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 207
    simpa using h
  have hprev := st168_p207
  have hstep := st168_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p209 : ((1278128637217/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT168 (i+1))
      = (∑ i ∈ Finset.range 208, stT168 (i+1)) + stT168 209 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 208
    simpa using h
  have hprev := st168_p208
  have hstep := st168_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p210 : ((672904347137/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT168 (i+1))
      = (∑ i ∈ Finset.range 209, stT168 (i+1)) + stT168 210 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 209
    simpa using h
  have hprev := st168_p209
  have hstep := st168_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p211 : ((1753183666991/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT168 (i+1))
      = (∑ i ∈ Finset.range 210, stT168 (i+1)) + stT168 211 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 210
    simpa using h
  have hprev := st168_p210
  have hstep := st168_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p212 : ((3536169389767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT168 (i+1))
      = (∑ i ∈ Finset.range 211, stT168 (i+1)) + stT168 212 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 211
    simpa using h
  have hprev := st168_p211
  have hstep := st168_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p213 : ((3437177394181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT168 (i+1))
      = (∑ i ∈ Finset.range 212, stT168 (i+1)) + stT168 213 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 212
    simpa using h
  have hprev := st168_p212
  have hstep := st168_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p214 : ((817168275847/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT168 (i+1))
      = (∑ i ∈ Finset.range 213, stT168 (i+1)) + stT168 214 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 213
    simpa using h
  have hprev := st168_p213
  have hstep := st168_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p215 : ((97795162129/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT168 (i+1))
      = (∑ i ∈ Finset.range 214, stT168 (i+1)) + stT168 215 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 214
    simpa using h
  have hprev := st168_p214
  have hstep := st168_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p216 : ((1239874028197/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT168 (i+1))
      = (∑ i ∈ Finset.range 215, stT168 (i+1)) + stT168 216 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 215
    simpa using h
  have hprev := st168_p215
  have hstep := st168_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p217 : ((6391052266467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT168 (i+1))
      = (∑ i ∈ Finset.range 216, stT168 (i+1)) + stT168 217 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 216
    simpa using h
  have hprev := st168_p216
  have hstep := st168_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p218 : ((420190450887/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT168 (i+1))
      = (∑ i ∈ Finset.range 217, stT168 (i+1)) + stT168 218 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 217
    simpa using h
  have hprev := st168_p217
  have hstep := st168_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p219 : ((14014719680777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT168 (i+1))
      = (∑ i ∈ Finset.range 218, stT168 (i+1)) + stT168 219 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 218
    simpa using h
  have hprev := st168_p218
  have hstep := st168_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p220 : ((7085752666213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT168 (i+1))
      = (∑ i ∈ Finset.range 219, stT168 (i+1)) + stT168 220 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 219
    simpa using h
  have hprev := st168_p219
  have hstep := st168_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p221 : ((13833061347917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT168 (i+1))
      = (∑ i ∈ Finset.range 220, stT168 (i+1)) + stT168 221 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 220
    simpa using h
  have hprev := st168_p220
  have hstep := st168_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p222 : ((659448907507/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT168 (i+1))
      = (∑ i ∈ Finset.range 221, stT168 (i+1)) + stT168 222 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 221
    simpa using h
  have hprev := st168_p221
  have hstep := st168_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p223 : ((1259186932569/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT168 (i+1))
      = (∑ i ∈ Finset.range 222, stT168 (i+1)) + stT168 223 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 222
    simpa using h
  have hprev := st168_p222
  have hstep := st168_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p224 : ((1236320698227/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT168 (i+1))
      = (∑ i ∈ Finset.range 223, stT168 (i+1)) + stT168 224 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 223
    simpa using h
  have hprev := st168_p223
  have hstep := st168_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p225 : ((6311117361621/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT168 (i+1))
      = (∑ i ∈ Finset.range 224, stT168 (i+1)) + stT168 225 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 224
    simpa using h
  have hprev := st168_p224
  have hstep := st168_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p226 : ((3306937798383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT168 (i+1))
      = (∑ i ∈ Finset.range 225, stT168 (i+1)) + stT168 226 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 225
    simpa using h
  have hprev := st168_p225
  have hstep := st168_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p227 : ((6929387608107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT168 (i+1))
      = (∑ i ∈ Finset.range 226, stT168 (i+1)) + stT168 227 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 226
    simpa using h
  have hprev := st168_p226
  have hstep := st168_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p228 : ((177328164627/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT168 (i+1))
      = (∑ i ∈ Finset.range 227, stT168 (i+1)) + stT168 228 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 227
    simpa using h
  have hprev := st168_p227
  have hstep := st168_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p229 : ((3510834791667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT168 (i+1))
      = (∑ i ∈ Finset.range 228, stT168 (i+1)) + stT168 229 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 228
    simpa using h
  have hprev := st168_p228
  have hstep := st168_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p230 : ((6753484164871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT168 (i+1))
      = (∑ i ∈ Finset.range 229, stT168 (i+1)) + stT168 230 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 229
    simpa using h
  have hprev := st168_p229
  have hstep := st168_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p231 : ((257056372687/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT168 (i+1))
      = (∑ i ∈ Finset.range 230, stT168 (i+1)) + stT168 231 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 230
    simpa using h
  have hprev := st168_p230
  have hstep := st168_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p232 : ((12411509625877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT168 (i+1))
      = (∑ i ∈ Finset.range 231, stT168 (i+1)) + stT168 232 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 231
    simpa using h
  have hprev := st168_p231
  have hstep := st168_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p233 : ((12401978911021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT168 (i+1))
      = (∑ i ∈ Finset.range 232, stT168 (i+1)) + stT168 233 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 232
    simpa using h
  have hprev := st168_p232
  have hstep := st168_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p234 : ((12825576396621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT168 (i+1))
      = (∑ i ∈ Finset.range 233, stT168 (i+1)) + stT168 234 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 233
    simpa using h
  have hprev := st168_p233
  have hstep := st168_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p235 : ((2694121360657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT168 (i+1))
      = (∑ i ∈ Finset.range 234, stT168 (i+1)) + stT168 235 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 234
    simpa using h
  have hprev := st168_p234
  have hstep := st168_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p236 : ((2804140660817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT168 (i+1))
      = (∑ i ∈ Finset.range 235, stT168 (i+1)) + stT168 236 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 235
    simpa using h
  have hprev := st168_p235
  have hstep := st168_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p237 : ((14210424221053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT168 (i+1))
      = (∑ i ∈ Finset.range 236, stT168 (i+1)) + stT168 237 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 236
    simpa using h
  have hprev := st168_p236
  have hstep := st168_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p238 : ((2790293085329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT168 (i+1))
      = (∑ i ∈ Finset.range 237, stT168 (i+1)) + stT168 238 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 237
    simpa using h
  have hprev := st168_p237
  have hstep := st168_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p239 : ((13370529548557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT168 (i+1))
      = (∑ i ∈ Finset.range 238, stT168 (i+1)) + stT168 239 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 238
    simpa using h
  have hprev := st168_p238
  have hstep := st168_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p240 : ((12744431990947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT168 (i+1))
      = (∑ i ∈ Finset.range 239, stT168 (i+1)) + stT168 240 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 239
    simpa using h
  have hprev := st168_p239
  have hstep := st168_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p241 : ((6183424851521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT168 (i+1))
      = (∑ i ∈ Finset.range 240, stT168 (i+1)) + stT168 241 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 240
    simpa using h
  have hprev := st168_p240
  have hstep := st168_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p242 : ((6205696453237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT168 (i+1))
      = (∑ i ∈ Finset.range 241, stT168 (i+1)) + stT168 242 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 241
    simpa using h
  have hprev := st168_p241
  have hstep := st168_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p243 : ((6427158290737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT168 (i+1))
      = (∑ i ∈ Finset.range 242, stT168 (i+1)) + stT168 243 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 242
    simpa using h
  have hprev := st168_p242
  have hstep := st168_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p244 : ((6744983079101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT168 (i+1))
      = (∑ i ∈ Finset.range 243, stT168 (i+1)) + stT168 244 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 243
    simpa using h
  have hprev := st168_p243
  have hstep := st168_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p245 : ((1402834249127/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT168 (i+1))
      = (∑ i ∈ Finset.range 244, stT168 (i+1)) + stT168 245 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 244
    simpa using h
  have hprev := st168_p244
  have hstep := st168_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p246 : ((7113840632623/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT168 (i+1))
      = (∑ i ∈ Finset.range 245, stT168 (i+1)) + stT168 246 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 245
    simpa using h
  have hprev := st168_p245
  have hstep := st168_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p247 : ((14001415137821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT168 (i+1))
      = (∑ i ∈ Finset.range 246, stT168 (i+1)) + stT168 247 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 246
    simpa using h
  have hprev := st168_p246
  have hstep := st168_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p248 : ((1681627502401/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT168 (i+1))
      = (∑ i ∈ Finset.range 247, stT168 (i+1)) + stT168 248 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 247
    simpa using h
  have hprev := st168_p247
  have hstep := st168_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p249 : ((12826148755083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT168 (i+1))
      = (∑ i ∈ Finset.range 248, stT168 (i+1)) + stT168 249 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 248
    simpa using h
  have hprev := st168_p248
  have hstep := st168_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_p250 : ((12395062318291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT168 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT168 (i+1))
      = (∑ i ∈ Finset.range 249, stT168 (i+1)) + stT168 250 := by
    have h := Finset.sum_range_succ (fun i => stT168 (i+1)) 249
    simpa using h
  have hprev := st168_p249
  have hstep := st168_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st168_s250 :
    |Real.sin (((168 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))
      - ((-146353/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -362607/625000) (δ := 529/62500000) (ψ := 14699/1000000) 168 148
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 168`** (evaluated boundary). -/
theorem station_168_sign : hardyG ((((168:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 168 250 (by norm_num) (by norm_num)
    ((14699/1000000 : ℚ) : ℝ)
  have hchain := st168_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT168 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((168 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((14699/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st168_c250
  have hsinb := abs_le.mp st168_s250
  have hbdy_lo : ((31184806155777/451588000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((168 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((14699/1000000 : ℚ) : ℝ))) / 2
          - ((((168:ℕ)):ℝ))
            * Real.sin (((168 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((14699/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((168:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((168:ℝ) * Real.log (250:ℝ) - ((14699/1000000 : ℚ) : ℝ))) / 2
        - ((168:ℝ)) * Real.sin ((168:ℝ) * Real.log (250:ℝ) - ((14699/1000000 : ℚ) : ℝ))
        ≥ ((246537747/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((168:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((246537747/2000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((246537747/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((246537747/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((168:ℕ)):ℝ))+1) * (((((168:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((120176047783/187500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12395062318291/10000000000000 : ℚ) : ℝ) + ((31184806155777/451588000000000 : ℚ) : ℝ)
      - ((120176047783/187500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((14699/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((168:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((14699/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((168:ℕ)):ℝ)))).re
      - Real.sin ((14699/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((168:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((168:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((168:ℕ)):ℝ))
      = (((((168:ℕ)):ℝ)) * (Real.log ((((168:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((168:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_168
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
  have hθwin : |(((14699/1000000 : ℚ) : ℝ) + ((31:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((168:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((168:ℕ)):ℝ)))
    (φ := ((14699/1000000 : ℚ) : ℝ) + ((31:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((14699/1000000 : ℚ) : ℝ) + ((31:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((14699/1000000 : ℚ)) : ℝ) - Real.pi) + ((31:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((14699/1000000 : ℚ)) : ℝ) - Real.pi) 31).1,
    (cos_sin_shift ((((14699/1000000 : ℚ)) : ℝ) - Real.pi) 31).2]
  exact cos_sin_flip ((14699/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_168_sign
end AxiomAudit
