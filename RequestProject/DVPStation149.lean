import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 149` (rung-154.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT149 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((149 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((771483/1000000 : ℚ) : ℝ))

theorem st149_c1 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((716877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482177/2500000) (δ := 201/1000000000) (ψ := 771483/1000000) 149 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t1 : ((716827/1000000 : ℚ) : ℝ) ≤ stT149 1 := by
  have hc : ((716827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((716827/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((716827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c2 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-78929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2470597/5000000) (δ := 119/15625000) (ψ := 771483/1000000) 149 16
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t2 : ((-139545759213/500000000000 : ℚ) : ℝ) ≤ stT149 2 := by
  have hc : ((-78939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139545759213/500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-78939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c3 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((904293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102689/10000000) (δ := 1897/250000000) (ψ := 771483/1000000) 149 26
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t3 : ((2610324384493/5000000000000 : ℚ) : ℝ) ≤ stT149 3 := by
  have hc : ((904243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2610324384493/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((904243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c4 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((1507/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -77937/200000) (δ := 1493/200000000) (ψ := 771483/1000000) 149 33
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t4 : ((6003/1000000 : ℚ) : ℝ) ≤ stT149 4 := by
  have hc : ((6003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6003/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((6003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c5 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((962769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27373/400000) (δ := 3787/500000000) (ψ := 771483/1000000) 149 38
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t5 : ((861081867013/2000000000000 : ℚ) : ℝ) ≤ stT149 5 := by
  have hc : ((962719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((861081867013/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((962719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c6 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-3357/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 576723/1000000) (δ := 19/2500000) (ψ := 771483/1000000) 149 42
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t6 : ((-54823664207/200000000000 : ℚ) : ℝ) ≤ stT149 6 := by
  have hc : ((-13429/20000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54823664207/200000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-13429/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c7 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((989849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 356513/10000000) (δ := 7471/1000000000) (ψ := 771483/1000000) 149 46
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t7 : ((935271962889/2500000000000 : ℚ) : ℝ) ≤ stT149 7 := by
  have hc : ((989799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((935271962889/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((989799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c8 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((46547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 297307/1000000) (δ := 7553/1000000000) (ψ := 771483/1000000) 149 49
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t8 : ((658185429879/5000000000000 : ℚ) : ℝ) ≤ stT149 8 := by
  have hc : ((186163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((658185429879/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((186163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c9 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((993883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -276653/10000000) (δ := 1907/250000000) (ψ := 771483/1000000) 149 52
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t9 : ((3312776335389/10000000000000 : ℚ) : ℝ) ≤ stT149 9 := by
  have hc : ((993833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3312776335389/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((993833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c10 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-992819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7554207/10000000) (δ := 3757/500000000) (ψ := 771483/1000000) 149 54
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t10 : ((-1569863897791/5000000000000 : ℚ) : ℝ) ≤ stT149 10 := by
  have hc : ((-992869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1569863897791/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-992869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c11 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-13957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4066633/10000000) (δ := 7511/1000000000) (ψ := 771483/1000000) 149 57
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t11 : ((-42119635023/2500000000000 : ℚ) : ℝ) ≤ stT149 11 := by
  have hc : ((-27939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42119635023/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-27939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c12 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((41977/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3070813/10000000) (δ := 301/40000000) (ψ := 771483/1000000) 149 59
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t12 : ((484636418133/5000000000000 : ℚ) : ℝ) ≤ stT149 12 := by
  have hc : ((167883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484636418133/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((167883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c13 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-293167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2335417/5000000) (δ := 933/125000000) (ψ := 771483/1000000) 149 61
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t13 : ((-813237642717/10000000000000 : ℚ) : ℝ) ≤ stT149 13 := by
  have hc : ((-293217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-813237642717/10000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-293217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c14 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-48433/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7226433/10000000) (δ := 7547/1000000000) (ψ := 771483/1000000) 149 62
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t14 : ((-258898693923/1000000000000 : ℚ) : ℝ) ≤ stT149 14 := by
  have hc : ((-96871/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258898693923/1000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-96871/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c15 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((205747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510361/10000000) (δ := 3821/500000000) (ψ := 771483/1000000) 149 64
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t15 : ((265602005093/1250000000000 : ℚ) : ℝ) ≤ stT149 15 := by
  have hc : ((411469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265602005093/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((411469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c16 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-349927/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2932487/5000000) (δ := 941/125000000) (ψ := 771483/1000000) 149 66
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t16 : ((-3417501367/19531250000 : ℚ) : ℝ) ≤ stT149 16 := by
  have hc : ((-10936/15625 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3417501367/19531250000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-10936/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c17 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((919539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 504863/5000000) (δ := 381/50000000) (ψ := 771483/1000000) 149 67
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t17 : ((557522040771/2500000000000 : ℚ) : ℝ) ≤ stT149 17 := by
  have hc : ((919489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((557522040771/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((919489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c18 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-2736/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6593267/10000000) (δ := 7513/1000000000) (ψ := 771483/1000000) 149 68
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t18 : ((-206373862811/1000000000000 : ℚ) : ℝ) ≤ stT149 18 := by
  have hc : ((-87557/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206373862811/1000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-87557/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c19 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-297673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4682627/10000000) (δ := 1901/250000000) (ψ := 771483/1000000) 149 70
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t19 : ((-341511801117/5000000000000 : ℚ) : ℝ) ≤ stT149 19 := by
  have hc : ((-297723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341511801117/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-297723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c20 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((435507/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -320959/2500000) (δ := 7611/1000000000) (ψ := 771483/1000000) 149 71
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t20 : ((486883464647/2500000000000 : ℚ) : ℝ) ≤ stT149 20 := by
  have hc : ((217741/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486883464647/2500000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((217741/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c21 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((890197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23651/200000) (δ := 3759/500000000) (ψ := 771483/1000000) 149 72
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t21 : ((971229600083/5000000000000 : ℚ) : ℝ) ≤ stT149 21 := by
  have hc : ((890147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((971229600083/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((890147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c22 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((434499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2803287/10000000) (δ := 3813/500000000) (ψ := 771483/1000000) 149 73
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t22 : ((926248309143/10000000000000 : ℚ) : ℝ) ≤ stT149 22 := by
  have hc : ((434449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((926248309143/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((434449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c23 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((109131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3653619/10000000) (δ := 7533/1000000000) (ψ := 771483/1000000) 149 74
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t23 : ((28431199083/1250000000000 : ℚ) : ℝ) ≤ stT149 23 := by
  have hc : ((109081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28431199083/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((109081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c24 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((51131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3799107/10000000) (δ := 191/25000000) (ψ := 771483/1000000) 149 75
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t24 : ((104268631521/10000000000000 : ℚ) : ℝ) ≤ stT149 24 := by
  have hc : ((51081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104268631521/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((51081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c25 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((249207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1648669/5000000) (δ := 1889/250000000) (ψ := 771483/1000000) 149 76
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t25 : ((249157/5000000 : ℚ) : ℝ) ≤ stT149 25 := by
  have hc : ((249157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249157/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((249157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c26 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((637433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1099543/5000000) (δ := 3777/500000000) (ψ := 771483/1000000) 149 77
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t26 : ((1250010681663/10000000000000 : ℚ) : ℝ) ≤ stT149 26 := by
  have hc : ((637383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1250010681663/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((637383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c27 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((975951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68673/1250000) (δ := 7541/1000000000) (ψ := 771483/1000000) 149 78
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t27 : ((3756242949/20000000000 : ℚ) : ℝ) ≤ stT149 27 := by
  have hc : ((975901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3756242949/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((975901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c28 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((399657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1611611/10000000) (δ := 3767/500000000) (ψ := 771483/1000000) 149 79
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t28 : ((23601042047/156250000000 : ℚ) : ℝ) ≤ stT149 28 := by
  have hc : ((24977/31250 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23601042047/156250000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((24977/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c29 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-128077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -849613/2000000) (δ := 7527/1000000000) (ψ := 771483/1000000) 149 80
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t29 : ((-118962972579/5000000000000 : ℚ) : ℝ) ≤ stT149 29 := by
  have hc : ((-128127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118962972579/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-128127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c30 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-488963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7327719/10000000) (δ := 7583/1000000000) (ψ := 771483/1000000) 149 81
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t30 : ((-111595741137/625000000000 : ℚ) : ℝ) ≤ stT149 30 := by
  have hc : ((-122247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111595741137/625000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-122247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c31 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-374457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2443259/5000000) (δ := 381/50000000) (ψ := 771483/1000000) 149 81
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t31 : ((-336317397689/5000000000000 : ℚ) : ℝ) ≤ stT149 31 := by
  have hc : ((-374507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336317397689/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-374507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c32 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((920289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502473/5000000) (δ := 749/100000000) (ψ := 771483/1000000) 149 82
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t32 : ((813383608037/5000000000000 : ℚ) : ℝ) ≤ stT149 32 := by
  have hc : ((920239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((813383608037/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((920239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c33 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((271121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -810149/2500000) (δ := 7597/1000000000) (ψ := 771483/1000000) 149 83
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t33 : ((58984236387/1250000000000 : ℚ) : ℝ) ≤ stT149 33 := by
  have hc : ((271071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58984236387/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((271071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c34 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-999947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7828317/10000000) (δ := 1501/200000000) (ψ := 771483/1000000) 149 84
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t34 : ((-857490427521/5000000000000 : ℚ) : ℝ) ≤ stT149 34 := by
  have hc : ((-999997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-857490427521/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-999997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c35 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((373691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2969527/10000000) (δ := 1521/200000000) (ψ := 771483/1000000) 149 84
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t35 : ((157892092857/2500000000000 : ℚ) : ℝ) ≤ stT149 35 := by
  have hc : ((373641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157892092857/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((373641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c36 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((124649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -280597/1250000) (δ := 1903/250000000) (ψ := 771483/1000000) 149 85
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t36 : ((103865791787/1000000000000 : ℚ) : ℝ) ≤ stT149 36 := by
  have hc : ((124639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103865791787/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((124639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c37 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-499539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1936653/2500000) (δ := 7519/1000000000) (ψ := 771483/1000000) 149 86
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t37 : ((-20531955509/125000000000 : ℚ) : ℝ) ≤ stT149 37 := by
  have hc : ((-124891/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20531955509/125000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-124891/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c38 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((641061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 546823/2500000) (δ := 237/31250000) (ψ := 771483/1000000) 149 86
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t38 : ((519928509177/5000000000000 : ℚ) : ℝ) ≤ stT149 38 := by
  have hc : ((641011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519928509177/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((641011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c39 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((4109/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3844797/10000000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 87
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t39 : ((26278622491/5000000000000 : ℚ) : ℝ) ≤ stT149 39 := by
  have hc : ((16411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26278622491/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((16411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c40 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-307993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5586083/10000000) (δ := 7577/1000000000) (ψ := 771483/1000000) 149 87
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t40 : ((-243509636251/2500000000000 : ℚ) : ℝ) ≤ stT149 40 := by
  have hc : ((-154009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-243509636251/2500000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-154009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c41 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((116561/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -461943/5000000) (δ := 7633/1000000000) (ψ := 771483/1000000) 149 88
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t41 : ((728111462403/5000000000000 : ℚ) : ℝ) ≤ stT149 41 := by
  have hc : ((466219/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((728111462403/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((466219/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c42 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-19937/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3827747/5000000) (δ := 7563/1000000000) (ψ := 771483/1000000) 149 89
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t42 : ((-7691252973/50000000000 : ℚ) : ℝ) ≤ stT149 42 := by
  have hc : ((-9969/10000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7691252973/50000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-9969/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c43 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((451553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 554809/5000000) (δ := 191/25000000) (ψ := 771483/1000000) 149 89
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t43 : ((17214335677/125000000000 : ℚ) : ℝ) ≤ stT149 43 := by
  have hc : ((56441/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17214335677/125000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((56441/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c44 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-746713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6034757/10000000) (δ := 1491/200000000) (ψ := 771483/1000000) 149 90
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t44 : ((-1125787787991/10000000000000 : ℚ) : ℝ) ≤ stT149 44 := by
  have hc : ((-746763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1125787787991/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-746763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c45 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((118837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2336361/10000000) (δ := 1491/200000000) (ψ := 771483/1000000) 149 90
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t45 : ((177136715997/2000000000000 : ℚ) : ℝ) ≤ stT149 45 := by
  have hc : ((118827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177136715997/2000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((118827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c46 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-241023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2592231/5000000) (δ := 1491/200000000) (ψ := 771483/1000000) 149 91
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t46 : ((-2221287451/31250000000 : ℚ) : ℝ) ≤ stT149 46 := by
  have hc : ((-30131/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2221287451/31250000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-30131/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c47 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((106517/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 565327/2000000) (δ := 1511/200000000) (ψ := 771483/1000000) 149 91
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t47 : ((310705364841/5000000000000 : ℚ) : ℝ) ≤ stT149 47 := by
  have hc : ((213009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310705364841/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((213009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c48 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-215129/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5038937/10000000) (δ := 3731/500000000) (ψ := 771483/1000000) 149 92
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t48 : ((-9704628747/156250000000 : ℚ) : ℝ) ≤ stT149 48 := by
  have hc : ((-107577/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9704628747/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-107577/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c49 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((6147/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 528343/2000000) (δ := 3731/500000000) (ψ := 771483/1000000) 149 92
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t49 : ((70244264641/1000000000000 : ℚ) : ℝ) ≤ stT149 49 := by
  have hc : ((49171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70244264641/1000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((49171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c50 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-300793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108141/2000000) (δ := 7569/1000000000) (ψ := 771483/1000000) 149 93
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t50 : ((-106355256763/1250000000000 : ℚ) : ℝ) ≤ stT149 50 := by
  have hc : ((-150409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-106355256763/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-150409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c51 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((92787/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1835763/10000000) (δ := 3767/500000000) (ψ := 771483/1000000) 149 93
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t51 : ((12991902861/125000000000 : ℚ) : ℝ) ≤ stT149 51 := by
  have hc : ((371123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12991902861/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((371123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c52 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-221051/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3319479/5000000) (δ := 7527/1000000000) (ψ := 771483/1000000) 149 94
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t52 : ((-613120059377/5000000000000 : ℚ) : ℝ) ≤ stT149 52 := by
  have hc : ((-442127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-613120059377/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-442127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c53 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((7867/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 456497/10000000) (δ := 947/125000000) (ψ := 771483/1000000) 149 94
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t53 : ((10805601093/80000000000 : ℚ) : ℝ) ≤ stT149 53 := by
  have hc : ((39333/40000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10805601093/80000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((39333/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c54 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-492461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927413/1250000) (δ := 1869/250000000) (ψ := 771483/1000000) 149 94
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t54 : ((-83773592301/625000000000 : ℚ) : ℝ) ≤ stT149 54 := by
  have hc : ((-246243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83773592301/625000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-246243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c55 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((208917/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -72681/500000) (δ := 7619/1000000000) (ψ := 771483/1000000) 149 95
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t55 : ((563373237791/5000000000000 : ℚ) : ℝ) ≤ stT149 55 := by
  have hc : ((417809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563373237791/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((417809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c56 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-5077/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164321/312500) (δ := 237/31250000) (ψ := 771483/1000000) 149 95
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t56 : ((-2714039517/40000000000 : ℚ) : ℝ) ≤ stT149 56 := by
  have hc : ((-2031/4000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2714039517/40000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-2031/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c57 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((7039/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3856591/10000000) (δ := 1903/250000000) (ψ := 771483/1000000) 149 96
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t57 : ((4653412049/1250000000000 : ℚ) : ℝ) ≤ stT149 57 := by
  have hc : ((14053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4653412049/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((14053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c58 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((249331/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 524371/2000000) (δ := 7491/1000000000) (ψ := 771483/1000000) 149 96
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t58 : ((20459670849/312500000000 : ℚ) : ℝ) ≤ stT149 58 := by
  have hc : ((124653/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20459670849/312500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((124653/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c59 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-449303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1679611/2500000) (δ := 3799/500000000) (ψ := 771483/1000000) 149 97
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t59 : ((-3656097687/31250000000 : ℚ) : ℝ) ≤ stT149 59 := by
  have hc : ((-28083/31250 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3656097687/31250000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-28083/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c60 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((12291/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2289/50000) (δ := 1521/200000000) (ψ := 771483/1000000) 149 97
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t60 : ((63467201531/500000000000 : ℚ) : ℝ) ≤ stT149 60 := by
  have hc : ((98323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63467201531/500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((98323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c61 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-651037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1139873/2000000) (δ := 3799/500000000) (ψ := 771483/1000000) 149 97
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t61 : ((-833631611103/10000000000000 : ℚ) : ℝ) ≤ stT149 61 := by
  have hc : ((-651087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-833631611103/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-651087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c62 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-2457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1975781/5000000) (δ := 1521/200000000) (ψ := 771483/1000000) 149 98
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t62 : ((-3136269939/2500000000000 : ℚ) : ℝ) ≤ stT149 62 := by
  have hc : ((-4939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3136269939/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-4939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c63 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((694239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2008587/10000000) (δ := 1521/200000000) (ψ := 771483/1000000) 149 98
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t63 : ((874595531509/10000000000000 : ℚ) : ℝ) ≤ stT149 63 := by
  have hc : ((694189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((874595531509/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((694189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c64 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-199993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1566627/2000000) (δ := 7491/1000000000) (ψ := 771483/1000000) 149 99
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t64 : ((-250003950003/2000000000000 : ℚ) : ℝ) ≤ stT149 64 := by
  have hc : ((-200003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250003950003/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-200003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c65 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((679931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102891/500000) (δ := 1903/250000000) (ψ := 771483/1000000) 149 99
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t65 : ((843288358707/10000000000000 : ℚ) : ℝ) ≤ stT149 65 := by
  have hc : ((679881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((843288358707/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((679881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c66 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((59393/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3629323/10000000) (δ := 7591/1000000000) (ψ := 771483/1000000) 149 99
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t66 : ((4567306397/312500000000 : ℚ) : ℝ) ≤ stT149 66 := by
  have hc : ((7421/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4567306397/312500000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((7421/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c67 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-170423/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3238511/5000000) (δ := 7519/1000000000) (ψ := 771483/1000000) 149 100
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t67 : ((-41643428787/400000000000 : ℚ) : ℝ) ≤ stT149 67 := by
  have hc : ((-170433/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41643428787/400000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-170433/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c68 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((463707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -958397/10000000) (δ := 7619/1000000000) (ψ := 771483/1000000) 149 100
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t68 : ((140574240099/1250000000000 : ℚ) : ℝ) ≤ stT149 68 := by
  have hc : ((231841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140574240099/1250000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((231841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c69 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-21927/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 559957/1250000) (δ := 7619/1000000000) (ψ := 771483/1000000) 149 100
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t69 : ((-6600758897/250000000000 : ℚ) : ℝ) ≤ stT149 69 := by
  have hc : ((-5483/25000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6600758897/250000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-5483/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c70 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-350433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5868517/10000000) (δ := 1869/250000000) (ψ := 771483/1000000) 149 101
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t70 : ((-209438782441/2500000000000 : ℚ) : ℝ) ≤ stT149 70 := by
  have hc : ((-175229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209438782441/2500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-175229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c71 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((97277/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -584753/10000000) (δ := 7627/1000000000) (ψ := 771483/1000000) 149 101
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t71 : ((14430070179/125000000000 : ℚ) : ℝ) ≤ stT149 71 := by
  have hc : ((12159/12500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14430070179/125000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((12159/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c72 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-55129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4625143/10000000) (δ := 947/125000000) (ψ := 771483/1000000) 149 101
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t72 : ((-4061373323/125000000000 : ℚ) : ℝ) ≤ stT149 72 := by
  have hc : ((-55139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4061373323/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-55139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c73 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-144461/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -371551/625000) (δ := 7569/1000000000) (ψ := 771483/1000000) 149 102
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t73 : ((-42272648013/500000000000 : ℚ) : ℝ) ≤ stT149 73 := by
  have hc : ((-144471/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42272648013/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-144471/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c74 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((187827/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87673/1000000) (δ := 7569/1000000000) (ψ := 771483/1000000) 149 102
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t74 : ((54583188723/500000000000 : ℚ) : ℝ) ≤ stT149 74 := by
  have hc : ((187817/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54583188723/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((187817/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c75 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-78473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 32987/80000) (δ := 7469/1000000000) (ψ := 771483/1000000) 149 102
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t75 : ((-90670586623/10000000000000 : ℚ) : ℝ) ≤ stT149 75 := by
  have hc : ((-78523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90670586623/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-78523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c76 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-886397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6650751/10000000) (δ := 7541/1000000000) (ψ := 771483/1000000) 149 103
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t76 : ((-1016824738313/10000000000000 : ℚ) : ℝ) ≤ stT149 76 := by
  have hc : ((-886447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1016824738313/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-886447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c77 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((189173/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -890697/5000000) (δ := 3731/500000000) (ψ := 771483/1000000) 149 103
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t77 : ((86227300641/1000000000000 : ℚ) : ℝ) ≤ stT149 77 := by
  have hc : ((378321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86227300641/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((378321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c78 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((352973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3025123/10000000) (δ := 7641/1000000000) (ψ := 771483/1000000) 149 103
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t78 : ((399606595671/10000000000000 : ℚ) : ℝ) ≤ stT149 78 := by
  have hc : ((352923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399606595671/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((352923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c79 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-999441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9713/12500) (δ := 3731/500000000) (ψ := 771483/1000000) 149 103
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t79 : ((-35141104069/312500000000 : ℚ) : ℝ) ≤ stT149 79 := by
  have hc : ((-999491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35141104069/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-999491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c80 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((266743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81299/250000) (δ := 1887/250000000) (ψ := 771483/1000000) 149 104
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t80 : ((298171574869/10000000000000 : ℚ) : ℝ) ≤ stT149 80 := by
  have hc : ((266693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((298171574869/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((266693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c81 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((213109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1375421/10000000) (δ := 1491/200000000) (ψ := 771483/1000000) 149 104
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t81 : ((473547730423/5000000000000 : ℚ) : ℝ) ≤ stT149 81 := by
  have hc : ((426193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473547730423/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((426193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c82 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-361321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5946033/10000000) (δ := 1511/200000000) (ψ := 771483/1000000) 149 104
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t82 : ((-49880021167/625000000000 : ℚ) : ℝ) ≤ stT149 82 := by
  have hc : ((-180673/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49880021167/625000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-180673/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c83 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-503709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5246709/10000000) (δ := 239/31250000) (ψ := 771483/1000000) 149 105
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t83 : ((-552947540037/10000000000000 : ℚ) : ℝ) ≤ stT149 83 := by
  have hc : ((-503759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552947540037/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-503759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c84 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((118879/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -785593/10000000) (δ := 1881/125000000) (ψ := 771483/1000000) 149 105
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t84 : ((518802999699/5000000000000 : ℚ) : ℝ) ≤ stT149 84 := by
  have hc : ((475491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((518802999699/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((475491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c85 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((607/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181137/500000) (δ := 1491/200000000) (ψ := 771483/1000000) 149 105
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t85 : ((658112601/50000000000 : ℚ) : ℝ) ≤ stT149 85 := by
  have hc : ((2427/20000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((658112601/50000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((2427/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c86 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-49937/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7728463/10000000) (δ := 7563/1000000000) (ψ := 771483/1000000) 149 106
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t86 : ((-13462790289/125000000000 : ℚ) : ℝ) ≤ stT149 86 := by
  have hc : ((-99879/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13462790289/125000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-99879/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c87 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((100307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -855507/2500000) (δ := 7463/1000000000) (ψ := 771483/1000000) 149 106
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t87 : ((3359797987/156250000000 : ℚ) : ℝ) ≤ stT149 87 := by
  have hc : ((50141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3359797987/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((50141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c88 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((944717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 835163/10000000) (δ := 7563/1000000000) (ψ := 771483/1000000) 149 106
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t88 : ((1007017856001/10000000000000 : ℚ) : ℝ) ≤ stT149 88 := by
  have hc : ((944667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1007017856001/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((944667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c89 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-432167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2522113/5000000) (δ := 191/25000000) (ψ := 771483/1000000) 149 106
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t89 : ((-229074577783/5000000000000 : ℚ) : ℝ) ≤ stT149 89 := by
  have hc : ((-432217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229074577783/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-432217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c90 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-214309/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6501683/10000000) (δ := 7633/1000000000) (ψ := 771483/1000000) 149 107
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t90 : ((-451829585799/5000000000000 : ℚ) : ℝ) ≤ stT149 90 := by
  have hc : ((-428643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-451829585799/5000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-428643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c91 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((23129/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2385613/10000000) (δ := 1507/100000000) (ψ := 771483/1000000) 149 107
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t91 : ((6060916017/100000000000 : ℚ) : ℝ) ≤ stT149 91 := by
  have hc : ((23127/40000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6060916017/100000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((23127/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c92 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((781217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 842729/5000000) (δ := 757/100000000) (ψ := 771483/1000000) 149 107
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t92 : ((203605710381/2500000000000 : ℚ) : ℝ) ≤ stT149 92 := by
  have hc : ((781167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203605710381/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((781167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c93 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-655021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2856259/5000000) (δ := 747/100000000) (ψ := 771483/1000000) 149 107
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t93 : ((-84909647949/1250000000000 : ℚ) : ℝ) ≤ stT149 93 := by
  have hc : ((-655071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84909647949/1250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-655071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c94 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-740479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3005723/5000000) (δ := 7477/1000000000) (ψ := 771483/1000000) 149 108
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t94 : ((-381898951119/5000000000000 : ℚ) : ℝ) ≤ stT149 94 := by
  have hc : ((-740529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-381898951119/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-740529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c95 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((42279/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1034807/5000000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 108
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t95 : ((173496470723/2500000000000 : ℚ) : ℝ) ≤ stT149 95 := by
  have hc : ((338207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173496470723/2500000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((338207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c96 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((371793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 366189/2000000) (δ := 3813/500000000) (ψ := 771483/1000000) 149 108
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t96 : ((2371461601/31250000000 : ℚ) : ℝ) ≤ stT149 96 := by
  have hc : ((46471/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2371461601/31250000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((46471/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c97 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-16213/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355693/625000) (δ := 3813/500000000) (ψ := 771483/1000000) 149 108
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t97 : ((-65852360379/1000000000000 : ℚ) : ℝ) ≤ stT149 97 := by
  have hc : ((-64857/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65852360379/1000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-64857/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c98 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-49257/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6196329/10000000) (δ := 7619/1000000000) (ψ := 771483/1000000) 149 109
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t98 : ((-398082104393/5000000000000 : ℚ) : ℝ) ≤ stT149 98 := by
  have hc : ((-394081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-398082104393/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-394081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c99 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((568739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15091/62500) (δ := 7619/1000000000) (ψ := 771483/1000000) 149 109
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t99 : ((571553486493/10000000000000 : ℚ) : ℝ) ≤ stT149 99 := by
  have hc : ((568689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((571553486493/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((568689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c100 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((861961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1329177/10000000) (δ := 7519/1000000000) (ψ := 771483/1000000) 149 109
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t100 : ((861910138089/10000000000000 : ℚ) : ℝ) ≤ stT149 100 := by
  have hc : ((861911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((861910138089/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((861911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c101 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-429089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5035701/10000000) (δ := 7519/1000000000) (ψ := 771483/1000000) 149 109
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t101 : ((-213504806141/5000000000000 : ℚ) : ℝ) ≤ stT149 101 := by
  have hc : ((-429139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213504806141/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-429139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c102 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-942527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175057/250000) (δ := 7591/1000000000) (ψ := 771483/1000000) 149 110
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t102 : ((-233322682849/2500000000000 : ℚ) : ℝ) ≤ stT149 102 := by
  have hc : ((-942577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233322682849/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-942577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c103 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((110843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3368133/10000000) (δ := 7491/1000000000) (ψ := 771483/1000000) 149 110
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t103 : ((54596094561/2500000000000 : ℚ) : ℝ) ≤ stT149 103 := by
  have hc : ((55409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54596094561/2500000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((55409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c104 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((995737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9237/400000) (δ := 7591/1000000000) (ψ := 771483/1000000) 149 110
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t104 : ((48817537923/500000000000 : ℚ) : ℝ) ≤ stT149 104 := by
  have hc : ((995687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48817537923/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((995687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c105 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((52547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3795563/10000000) (δ := 1903/250000000) (ψ := 771483/1000000) 149 110
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t105 : ((512318223/100000000000 : ℚ) : ℝ) ≤ stT149 105 := by
  have hc : ((52497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((512318223/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((52497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c106 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-977813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7326379/10000000) (δ := 939/125000000) (ψ := 771483/1000000) 149 110
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t106 : ((-474892320909/5000000000000 : ℚ) : ℝ) ≤ stT149 106 := by
  have hc : ((-977863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474892320909/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-977863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c107 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-9337/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1220971/2500000) (δ := 1521/200000000) (ψ := 771483/1000000) 149 111
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t107 : ((-36110527161/1000000000000 : ℚ) : ℝ) ≤ stT149 107 := by
  have hc : ((-37353/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36110527161/1000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-37353/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c108 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((3373/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70937/500000) (δ := 1521/200000000) (ψ := 771483/1000000) 149 111
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t108 : ((2028423/25000000 : ℚ) : ℝ) ≤ stT149 108 := by
  have hc : ((527/625 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2028423/25000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((527/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c109 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((692551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 503611/2500000) (δ := 3749/500000000) (ψ := 771483/1000000) 149 111
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t109 : ((331647731413/5000000000000 : ℚ) : ℝ) ≤ stT149 109 := by
  have hc : ((692501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331647731413/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((692501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c110 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-140277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54163/100000) (δ := 1501/200000000) (ψ := 771483/1000000) 149 111
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t110 : ((-267521695077/5000000000000 : ℚ) : ℝ) ≤ stT149 110 := by
  have hc : ((-280579/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-267521695077/5000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-280579/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c111 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-465553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -276823/400000) (δ := 3803/500000000) (ψ := 771483/1000000) 149 112
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t111 : ((-110476770831/1250000000000 : ℚ) : ℝ) ≤ stT149 111 := by
  have hc : ((-232789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110476770831/1250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-232789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c112 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((138441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -894943/2500000) (δ := 7497/1000000000) (ψ := 771483/1000000) 149 112
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t112 : ((130767178201/10000000000000 : ℚ) : ℝ) ≤ stT149 112 := by
  have hc : ((138391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130767178201/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((138391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c113 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((994233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268619/10000000) (δ := 3803/500000000) (ψ := 771483/1000000) 149 112
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t113 : ((11690597897/125000000000 : ℚ) : ℝ) ≤ stT149 113 := by
  have hc : ((994183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11690597897/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((994183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c114 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((357383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3013329/10000000) (δ := 7497/1000000000) (ψ := 771483/1000000) 149 112
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t114 : ((66934545561/2000000000000 : ℚ) : ℝ) ≤ stT149 114 := by
  have hc : ((357333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66934545561/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((357333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c115 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-805107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 783329/1250000) (δ := 7597/1000000000) (ψ := 771483/1000000) 149 112
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t115 : ((-150162585657/2000000000000 : ℚ) : ℝ) ≤ stT149 115 := by
  have hc : ((-805157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-150162585657/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-805157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c116 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-396493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3108113/5000000) (δ := 749/100000000) (ψ := 771483/1000000) 149 113
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t116 : ((-184078921543/2500000000000 : ℚ) : ℝ) ≤ stT149 116 := by
  have hc : ((-198259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184078921543/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-198259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c117 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((177677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75469/250000) (δ := 7613/1000000000) (ψ := 771483/1000000) 149 113
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t117 : ((82119637/2500000000 : ℚ) : ℝ) ≤ stT149 117 := by
  have hc : ((44413/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82119637/2500000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((44413/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c118 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((199633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6059/400000) (δ := 759/100000000) (ψ := 771483/1000000) 149 113
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t118 : ((91883871801/1000000000000 : ℚ) : ℝ) ≤ stT149 118 := by
  have hc : ((199623/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91883871801/1000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((199623/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c119 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((12507/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205933/625000) (δ := 759/100000000) (ψ := 771483/1000000) 149 113
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t119 : ((11462850141/500000000000 : ℚ) : ℝ) ≤ stT149 119 := by
  have hc : ((25009/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11462850141/500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((25009/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c120 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-419121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160303/250000) (δ := 749/100000000) (ψ := 771483/1000000) 149 113
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t120 : ((-191313114083/2500000000000 : ℚ) : ℝ) ≤ stT149 120 := by
  have hc : ((-209573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191313114083/2500000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-209573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c121 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-790129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -310227/500000) (δ := 47/6250000) (ψ := 771483/1000000) 149 114
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t121 : ((-718344617289/10000000000000 : ℚ) : ℝ) ≤ stT149 121 := by
  have hc : ((-790179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-718344617289/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-790179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c122 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((2481/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3138679/10000000) (δ := 7483/1000000000) (ψ := 771483/1000000) 149 114
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t122 : ((11229142871/400000000000 : ℚ) : ℝ) ≤ stT149 122 := by
  have hc : ((12403/40000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11229142871/400000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((12403/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c123 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((499617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957/200000) (δ := 7583/1000000000) (ψ := 771483/1000000) 149 114
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t123 : ((56308327381/625000000000 : ℚ) : ℝ) ≤ stT149 123 := by
  have hc : ((62449/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56308327381/625000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((62449/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c124 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((392597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2918357/10000000) (δ := 7583/1000000000) (ψ := 771483/1000000) 149 114
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t124 : ((176258706111/5000000000000 : ℚ) : ℝ) ≤ stT149 124 := by
  have hc : ((392547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176258706111/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((392547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c125 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-712703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 369397/625000) (δ := 47/6250000) (ψ := 771483/1000000) 149 114
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t125 : ((-159376560071/2500000000000 : ℚ) : ℝ) ≤ stT149 125 := by
  have hc : ((-712753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159376560071/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-712753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c126 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-917197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6829457/10000000) (δ := 1869/250000000) (ψ := 771483/1000000) 149 115
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t126 : ((-817148752137/10000000000000 : ℚ) : ℝ) ≤ stT149 126 := by
  have hc : ((-917247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-817148752137/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-917247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c127 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((16873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3884807/10000000) (δ := 7527/1000000000) (ψ := 771483/1000000) 149 115
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t127 : ((3731997497/2500000000000 : ℚ) : ℝ) ≤ stT149 127 := by
  have hc : ((16823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3731997497/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((16823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c128 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((926691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192643/2000000) (δ := 7527/1000000000) (ψ := 771483/1000000) 149 115
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t128 : ((819042227003/10000000000000 : ℚ) : ℝ) ≤ stT149 128 := by
  have hc : ((926641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((819042227003/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((926641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c129 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((357469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 967827/5000000) (δ := 947/125000000) (ψ := 771483/1000000) 149 115
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t129 : ((1573557849/25000000000 : ℚ) : ℝ) ≤ stT149 129 := by
  have hc : ((89361/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1573557849/25000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((89361/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c130 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-346693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4812099/10000000) (δ := 947/125000000) (ψ := 771483/1000000) 149 115
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t130 : ((-304114068837/10000000000000 : ℚ) : ℝ) ≤ stT149 130 := by
  have hc : ((-346743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304114068837/10000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-346743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c131 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-99719/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 766653/1000000) (δ := 7627/1000000000) (ψ := 771483/1000000) 149 115
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t131 : ((-4356467871/50000000000 : ℚ) : ℝ) ≤ stT149 131 := by
  have hc : ((-24931/25000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4356467871/50000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-24931/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c132 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-19621/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65109/125000) (δ := 3767/500000000) (ψ := 771483/1000000) 149 116
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t132 : ((-17079643347/400000000000 : ℚ) : ℝ) ≤ stT149 132 := by
  have hc : ((-19623/40000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17079643347/400000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-19623/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c133 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((71797/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -599347/2500000) (δ := 3767/500000000) (ψ := 771483/1000000) 149 116
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t133 : ((249001621767/5000000000000 : ℚ) : ℝ) ≤ stT149 133 := by
  have hc : ((287163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249001621767/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((287163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c134 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((987677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 392879/10000000) (δ := 7467/500000000) (ψ := 771483/1000000) 149 116
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t134 : ((213294840309/2500000000000 : ℚ) : ℝ) ≤ stT149 134 := by
  have hc : ((987627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213294840309/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((987627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c135 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((75273/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1581199/5000000) (δ := 3767/500000000) (ψ := 771483/1000000) 149 116
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t135 : ((64773852451/2500000000000 : ℚ) : ℝ) ≤ stT149 135 := by
  have hc : ((150521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64773852451/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((150521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c136 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-713021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1182297/2000000) (δ := 7469/1000000000) (ψ := 771483/1000000) 149 116
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t136 : ((-611453391003/10000000000000 : ℚ) : ℝ) ≤ stT149 136 := by
  have hc : ((-713071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-611453391003/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-713071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c137 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-950923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3533753/5000000) (δ := 7461/1000000000) (ψ := 771483/1000000) 149 117
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t137 : ((-406235695167/5000000000000 : ℚ) : ℝ) ≤ stT149 137 := by
  have hc : ((-950973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406235695167/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-950973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c138 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-85859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174337/400000) (δ := 3771/500000000) (ψ := 771483/1000000) 149 117
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t138 : ((-18277339047/1250000000000 : ℚ) : ℝ) ≤ stT149 138 := by
  have hc : ((-21471/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18277339047/1250000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-21471/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c139 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((12271/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1668863/10000000) (δ := 3821/500000000) (ψ := 771483/1000000) 149 117
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t139 : ((83259618409/1250000000000 : ℚ) : ℝ) ≤ stT149 139 := by
  have hc : ((392647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83259618409/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((392647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c140 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((460421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1001403/10000000) (δ := 3771/500000000) (ψ := 771483/1000000) 149 117
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t140 : ((48638190123/625000000000 : ℚ) : ℝ) ≤ stT149 140 := by
  have hc : ((115099/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48638190123/625000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((115099/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c141 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((109523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1826317/5000000) (δ := 7561/1000000000) (ψ := 771483/1000000) 149 117
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t141 : ((92192796423/10000000000000 : ℚ) : ℝ) ≤ stT149 141 := by
  have hc : ((109473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92192796423/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((109473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c142 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-404741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3142583/5000000) (δ := 7561/1000000000) (ψ := 771483/1000000) 149 117
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t142 : ((-84918085353/1250000000000 : ℚ) : ℝ) ≤ stT149 142 := by
  have hc : ((-202383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84918085353/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-202383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c143 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-114233/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6808741/10000000) (δ := 3727/500000000) (ψ := 771483/1000000) 149 118
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t143 : ((-382127092551/5000000000000 : ℚ) : ℝ) ≤ stT149 143 := by
  have hc : ((-456957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382127092551/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-456957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c144 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-114129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4212937/10000000) (δ := 7649/1000000000) (ψ := 771483/1000000) 149 118
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t144 : ((-47574621393/5000000000000 : ℚ) : ℝ) ≤ stT149 144 := by
  have hc : ((-114179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47574621393/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-114179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c145 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((198411/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1635051/10000000) (δ := 7549/1000000000) (ψ := 771483/1000000) 149 118
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t145 : ((164760827919/2500000000000 : ℚ) : ℝ) ≤ stT149 145 := by
  have hc : ((396797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164760827919/2500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((396797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c146 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((116539/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57819/625000) (δ := 3727/500000000) (ψ := 771483/1000000) 149 118
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t146 : ((77154469251/1000000000000 : ℚ) : ℝ) ≤ stT149 146 := by
  have hc : ((466131/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77154469251/1000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((466131/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c147 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((22833/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 433469/1250000) (δ := 7549/1000000000) (ψ := 771483/1000000) 149 118
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t147 : ((37654367651/2500000000000 : ℚ) : ℝ) ≤ stT149 147 := by
  have hc : ((91307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37654367651/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((91307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c148 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-735551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599319/1000000) (δ := 3727/500000000) (ψ := 771483/1000000) 149 118
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t148 : ((-120932068799/2000000000000 : ℚ) : ℝ) ≤ stT149 148 := by
  have hc : ((-735601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120932068799/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-735601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c149 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-96663/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7206321/10000000) (δ := 233/31250000) (ψ := 771483/1000000) 149 119
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t149 : ((-618699367/7812500000 : ℚ) : ℝ) ≤ stT149 149 := by
  have hc : ((-24167/25000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618699367/7812500000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-24167/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c150 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-154949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2357353/5000000) (δ := 7547/1000000000) (ψ := 771483/1000000) 149 119
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t150 : ((-63267903039/2500000000000 : ℚ) : ℝ) ≤ stT149 150 := by
  have hc : ((-77487/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63267903039/2500000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-77487/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c151 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((312433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279949/1250000) (δ := 1889/250000000) (ψ := 771483/1000000) 149 119
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t151 : ((7944808797/156250000000 : ℚ) : ℝ) ≤ stT149 151 := by
  have hc : ((39051/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7944808797/156250000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((39051/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c152 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((3113/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6849/312500) (δ := 7647/1000000000) (ψ := 771483/1000000) 149 119
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t152 : ((80795179377/1000000000000 : ℚ) : ℝ) ≤ stT149 152 := by
  have hc : ((99611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80795179377/1000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((99611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c153 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((484749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13309/50000) (δ := 233/31250000) (ψ := 771483/1000000) 149 119
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t153 : ((97963968987/2500000000000 : ℚ) : ℝ) ≤ stT149 153 := by
  have hc : ((484699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97963968987/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((484699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c154 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-224039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2544263/5000000) (δ := 1889/250000000) (ψ := 771483/1000000) 149 119
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t154 : ((-2821186323/78125000000 : ℚ) : ℝ) ≤ stT149 154 := by
  have hc : ((-7002/15625 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2821186323/78125000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-7002/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c155 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-494983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1874883/2500000) (δ := 233/31250000) (ψ := 771483/1000000) 149 119
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t155 : ((-621250509/7812500000 : ℚ) : ℝ) ≤ stT149 155 := by
  have hc : ((-15469/15625 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-621250509/7812500000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-15469/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c156 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-684831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5812921/10000000) (δ := 7463/1000000000) (ψ := 771483/1000000) 149 120
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t156 : ((-548343808721/10000000000000 : ℚ) : ℝ) ≤ stT149 156 := by
  have hc : ((-684881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548343808721/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-684881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c157 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((98211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3432721/10000000) (δ := 191/25000000) (ψ := 771483/1000000) 149 120
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t157 : ((19590217999/1250000000000 : ℚ) : ℝ) ≤ stT149 157 := by
  have hc : ((49093/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19590217999/1250000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((49093/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c158 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((227547/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266911/2500000) (δ := 191/25000000) (ψ := 771483/1000000) 149 120
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t158 : ((362033328433/5000000000000 : ℚ) : ℝ) ≤ stT149 158 := by
  have hc : ((455069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362033328433/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((455069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c159 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((87127/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1282533/10000000) (δ := 191/25000000) (ψ := 771483/1000000) 149 120
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t159 : ((34546094611/500000000000 : ℚ) : ℝ) ≤ stT149 159 := by
  have hc : ((43561/50000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34546094611/500000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((43561/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c160 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((61649/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3617959/10000000) (δ := 191/25000000) (ψ := 771483/1000000) 149 120
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t160 : ((6089753007/625000000000 : ℚ) : ℝ) ≤ stT149 160 := by
  have hc : ((7703/62500 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6089753007/625000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((7703/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c161 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-144129/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5938821/10000000) (δ := 7563/1000000000) (ψ := 771483/1000000) 149 120
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t161 : ((-113597531429/2000000000000 : ℚ) : ℝ) ≤ stT149 161 := by
  have hc : ((-144139/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113597531429/2000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-144139/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c162 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-246943/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7462623/10000000) (δ := 7633/1000000000) (ψ := 771483/1000000) 149 121
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t162 : ((-15522140997/200000000000 : ℚ) : ℝ) ≤ stT149 162 := by
  have hc : ((-493911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15522140997/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-493911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c163 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-477073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1034059/2000000) (δ := 7533/1000000000) (ψ := 771483/1000000) 149 121
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t163 : ((-373711838103/10000000000000 : ℚ) : ℝ) ≤ stT149 163 := by
  have hc : ((-477123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-373711838103/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-477123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c164 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((100567/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -289201/1000000) (δ := 757/100000000) (ψ := 771483/1000000) 149 121
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t164 : ((39259895653/1250000000000 : ℚ) : ℝ) ≤ stT149 164 := by
  have hc : ((201109/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39259895653/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((201109/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c165 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((60541/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627583/10000000) (δ := 7533/1000000000) (ψ := 771483/1000000) 149 121
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t165 : ((188514458447/2500000000000 : ℚ) : ℝ) ≤ stT149 165 := by
  have hc : ((484303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188514458447/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((484303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c166 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((398263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811587/5000000) (δ := 747/100000000) (ψ := 771483/1000000) 149 121
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t166 : ((3090924237/50000000000 : ℚ) : ℝ) ≤ stT149 166 := by
  have hc : ((199119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3090924237/50000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((199119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c167 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((5323/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1930223/5000000) (δ := 7533/1000000000) (ψ := 771483/1000000) 149 121
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t167 : ((4111321599/2000000000000 : ℚ) : ℝ) ≤ stT149 167 := by
  have hc : ((5313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4111321599/2000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((5313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c168 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-759749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1521077/2500000) (δ := 7633/1000000000) (ψ := 771483/1000000) 149 121
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t168 : ((-586197845083/10000000000000 : ℚ) : ℝ) ≤ stT149 168 := by
  have hc : ((-759799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-586197845083/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-759799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c169 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-984479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3706471/5000000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 122
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t169 : ((-757330227199/10000000000000 : ℚ) : ℝ) ≤ stT149 169 := by
  have hc : ((-984529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-757330227199/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-984529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c170 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-246409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -651913/1250000) (δ := 3813/500000000) (ψ := 771483/1000000) 149 122
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t170 : ((-18900625281/500000000000 : ℚ) : ℝ) ≤ stT149 170 := by
  have hc : ((-123217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18900625281/500000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-123217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c171 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((17547/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1515277/5000000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 122
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t171 : ((26833224991/1000000000000 : ℚ) : ℝ) ≤ stT149 171 := by
  have hc : ((35089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26833224991/1000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((35089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c172 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((941609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53659/625000) (δ := 3813/500000000) (ψ := 771483/1000000) 149 122
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t172 : ((179482801257/2500000000000 : ℚ) : ℝ) ≤ stT149 172 := by
  have hc : ((941559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179482801257/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((941559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c173 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((173529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325219/2500000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 122
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t173 : ((26384778583/400000000000 : ℚ) : ℝ) ≤ stT149 173 := by
  have hc : ((173519/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26384778583/400000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((173519/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c174 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((47621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1723927/5000000) (δ := 3813/500000000) (ψ := 771483/1000000) 149 122
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t174 : ((36091908633/2500000000000 : ℚ) : ℝ) ≤ stT149 174 := by
  have hc : ((95217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36091908633/2500000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((95217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c175 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-614869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 279127/500000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 122
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t175 : ((-464835104751/10000000000000 : ℚ) : ℝ) ≤ stT149 175 := by
  have hc : ((-614919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-464835104751/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-614919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c176 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-499113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1541009/2000000) (δ := 3763/500000000) (ψ := 771483/1000000) 149 122
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t176 : ((-188119871251/2500000000000 : ℚ) : ℝ) ≤ stT149 176 := by
  have hc : ((-249569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188119871251/2500000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-249569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c177 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-14153/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -736551/1250000) (δ := 3809/500000000) (ψ := 771483/1000000) 149 123
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t177 : ((-5319405819/100000000000 : ℚ) : ℝ) ≤ stT149 177 := by
  have hc : ((-7077/10000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5319405819/100000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-7077/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c178 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((13311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3793817/10000000) (δ := 1497/200000000) (ψ := 771483/1000000) 149 123
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t178 : ((19935276007/5000000000000 : ℚ) : ℝ) ≤ stT149 178 := by
  have hc : ((26597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19935276007/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((26597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c179 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((775819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21337/125000) (δ := 1517/200000000) (ψ := 771483/1000000) 149 123
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t179 : ((115967380503/2000000000000 : ℚ) : ℝ) ≤ stT149 179 := by
  have hc : ((775769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115967380503/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((775769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c180 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((247293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 368237/10000000) (δ := 3759/500000000) (ψ := 771483/1000000) 149 123
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t180 : ((73724702831/1000000000000 : ℚ) : ℝ) ≤ stT149 180 := by
  have hc : ((494561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73724702831/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((494561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c181 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((563/1000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1215981/5000000) (δ := 1517/200000000) (ψ := 771483/1000000) 149 123
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t181 : ((4184373573/100000000000 : ℚ) : ℝ) ≤ stT149 181 := by
  have hc : ((11259/20000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4184373573/100000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((11259/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c182 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-221077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 70067/156250) (δ := 1517/200000000) (ψ := 771483/1000000) 149 123
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t182 : ((-131128311/8000000000 : ℚ) : ℝ) ≤ stT149 182 := by
  have hc : ((-221127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131128311/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-221127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c183 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-431041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6525401/10000000) (δ := 3809/500000000) (ψ := 771483/1000000) 149 123
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t183 : ((-79663367663/1250000000000 : ℚ) : ℝ) ≤ stT149 183 := by
  have hc : ((-215533/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79663367663/1250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-215533/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c184 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-960901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3576293/5000000) (δ := 7511/1000000000) (ψ := 771483/1000000) 149 124
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t184 : ((-70842268671/1000000000000 : ℚ) : ℝ) ≤ stT149 184 := by
  have hc : ((-960951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70842268671/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-960951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c185 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-232061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5133599/10000000) (δ := 7611/1000000000) (ψ := 771483/1000000) 149 124
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t185 : ((-17063310849/500000000000 : ℚ) : ℝ) ≤ stT149 185 := by
  have hc : ((-116043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17063310849/500000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-116043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c186 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((315123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1562763/5000000) (δ := 7611/1000000000) (ψ := 771483/1000000) 149 124
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t186 : ((46204510231/2000000000000 : ℚ) : ℝ) ≤ stT149 186 := by
  have hc : ((315073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46204510231/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((315073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c187 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((899893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1128181/10000000) (δ := 7611/1000000000) (ψ := 771483/1000000) 149 124
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t187 : ((82253748787/1250000000000 : ℚ) : ℝ) ≤ stT149 187 := by
  have hc : ((899843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82253748787/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((899843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c188 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((941619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 429237/5000000) (δ := 949/125000000) (ψ := 771483/1000000) 149 124
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t188 : ((171677217339/2500000000000 : ℚ) : ℝ) ≤ stT149 188 := by
  have hc : ((941569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171677217339/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((941569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c189 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((16927/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2834623/10000000) (δ := 7611/1000000000) (ψ := 771483/1000000) 149 124
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t189 : ((15388887/500000000 : ℚ) : ℝ) ≤ stT149 189 := by
  have hc : ((677/1600 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15388887/500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((677/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c190 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-68453/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2400153/5000000) (δ := 1873/250000000) (ψ := 771483/1000000) 149 124
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t190 : ((-49668331851/2000000000000 : ℚ) : ℝ) ≤ stT149 190 := by
  have hc : ((-68463/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49668331851/2000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-68463/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c191 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-181009/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6755707/10000000) (δ := 7611/1000000000) (ψ := 771483/1000000) 149 124
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t191 : ((-5239232917/80000000000 : ℚ) : ℝ) ≤ stT149 191 := by
  have hc : ((-181019/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5239232917/80000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-181019/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c192 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-94317/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3503549/5000000) (δ := 7499/1000000000) (ψ := 771483/1000000) 149 125
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t192 : ((-4254440971/62500000000 : ℚ) : ℝ) ≤ stT149 192 := by
  have hc : ((-47161/50000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4254440971/62500000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-47161/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c193 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-442171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1014407/2000000) (δ := 7499/1000000000) (ψ := 771483/1000000) 149 125
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t193 : ((-39789718917/1250000000000 : ℚ) : ℝ) ≤ stT149 193 := by
  have hc : ((-442221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39789718917/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-442221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c194 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((9593/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -629391/2000000) (δ := 7499/1000000000) (ψ := 771483/1000000) 149 125
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t194 : ((55089994277/2500000000000 : ℚ) : ℝ) ≤ stT149 194 := by
  have hc : ((153463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55089994277/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((153463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c195 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((881053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -153973/1250000) (δ := 1901/250000000) (ψ := 771483/1000000) 149 125
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t195 : ((315449291171/5000000000000 : ℚ) : ℝ) ≤ stT149 195 := by
  have hc : ((881003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315449291171/5000000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((881003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c196 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((963921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 673591/10000000) (δ := 469/62500000) (ψ := 771483/1000000) 149 125
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t196 : ((137695719447/2000000000000 : ℚ) : ℝ) ≤ stT149 196 := by
  have hc : ((963871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137695719447/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((963871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c197 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((516779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2569281/10000000) (δ := 7499/1000000000) (ψ := 771483/1000000) 149 125
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t197 : ((36815391063/1000000000000 : ℚ) : ℝ) ≤ stT149 197 := by
  have hc : ((516729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36815391063/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((516729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c198 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-104889/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13923/31250) (δ := 469/62500000) (ψ := 771483/1000000) 149 125
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t198 : ((-3727961619/250000000000 : ℚ) : ℝ) ≤ stT149 198 := by
  have hc : ((-52457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3727961619/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-52457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c199 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-410163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6331941/10000000) (δ := 7599/1000000000) (ψ := 771483/1000000) 149 125
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t199 : ((-36346861227/625000000000 : ℚ) : ℝ) ≤ stT149 199 := by
  have hc : ((-102547/125000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36346861227/625000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-102547/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c200 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-990487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3754433/5000000) (δ := 3803/500000000) (ψ := 771483/1000000) 149 126
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t200 : ((-700415646459/10000000000000 : ℚ) : ℝ) ≤ stT149 200 := by
  have hc : ((-990537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-700415646459/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-990537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c201 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-636227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1130197/2000000) (δ := 3803/500000000) (ψ := 771483/1000000) 149 126
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t201 : ((-224397718421/5000000000000 : ℚ) : ℝ) ≤ stT149 201 := by
  have hc : ((-636277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224397718421/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-636277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c202 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((1557/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190119/500000) (δ := 7597/1000000000) (ψ := 771483/1000000) 149 126
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t202 : ((17510418539/5000000000000 : ℚ) : ℝ) ≤ stT149 202 := by
  have hc : ((24887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17510418539/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((24887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c203 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((353643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1962863/10000000) (δ := 7497/1000000000) (ψ := 771483/1000000) 149 126
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t203 : ((62047759179/1250000000000 : ℚ) : ℝ) ≤ stT149 203 := by
  have hc : ((176809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62047759179/1250000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((176809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c204 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((499299/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66199/5000000) (δ := 7497/1000000000) (ψ := 771483/1000000) 149 126
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t204 : ((8739042459/125000000000 : ℚ) : ℝ) ≤ stT149 204 := by
  have hc : ((249637/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8739042459/125000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((249637/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c205 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((7803/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1689127/10000000) (δ := 7497/1000000000) (ψ := 771483/1000000) 149 126
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t205 : ((217980003/4000000000 : ℚ) : ℝ) ≤ stT149 205 := by
  have hc : ((3121/4000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217980003/4000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((3121/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c206 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((169263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3501787/10000000) (δ := 3803/500000000) (ψ := 771483/1000000) 149 126
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t206 : ((117896281129/10000000000000 : ℚ) : ℝ) ≤ stT149 206 := by
  have hc : ((169213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117896281129/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((169213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c207 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-16373/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1061131/2000000) (δ := 7497/1000000000) (ψ := 771483/1000000) 149 126
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t207 : ((-182097972657/5000000000000 : ℚ) : ℝ) ≤ stT149 207 := by
  have hc : ((-261993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182097972657/5000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-261993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c208 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-190993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1775211/2500000) (δ := 7597/1000000000) (ψ := 771483/1000000) 149 126
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t208 : ((-1034663251/15625000000 : ℚ) : ℝ) ≤ stT149 208 := by
  have hc : ((-191003/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1034663251/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-191003/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c209 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-915769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3410267/5000000) (δ := 7613/1000000000) (ψ := 771483/1000000) 149 127
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t209 : ((-126697147917/2000000000000 : ℚ) : ℝ) ≤ stT149 209 := by
  have hc : ((-915819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126697147917/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-915819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c210 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-431537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63031/125000) (δ := 7513/1000000000) (ψ := 771483/1000000) 149 127
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t210 : ((-148911757371/5000000000000 : ℚ) : ℝ) ≤ stT149 210 := by
  have hc : ((-431587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148911757371/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-431587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c211 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((64667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1636441/5000000) (δ := 759/100000000) (ψ := 771483/1000000) 149 127
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t211 : ((22254984063/1250000000000 : ℚ) : ℝ) ≤ stT149 211 := by
  have hc : ((129309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22254984063/1250000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((129309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c212 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((205673/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94479/625000) (δ := 7613/1000000000) (ψ := 771483/1000000) 149 127
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t212 : ((141248042721/2500000000000 : ℚ) : ℝ) ≤ stT149 212 := by
  have hc : ((411321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141248042721/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((411321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c213 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((497673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 241283/10000000) (δ := 759/100000000) (ψ := 771483/1000000) 149 127
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t213 : ((5327850591/78125000000 : ℚ) : ℝ) ≤ stT149 213 := by
  have hc : ((31103/31250 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5327850591/78125000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((31103/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c214 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((700703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 496509/2500000) (δ := 749/100000000) (ψ := 771483/1000000) 149 127
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t214 : ((95791176201/2000000000000 : ℚ) : ℝ) ≤ stT149 214 := by
  have hc : ((700653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95791176201/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((700653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c215 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((81653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3722631/10000000) (δ := 749/100000000) (ψ := 771483/1000000) 149 127
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t215 : ((27826378191/5000000000000 : ℚ) : ℝ) ≤ stT149 215 := by
  have hc : ((81603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27826378191/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((81603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c216 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-286301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272559/500000) (δ := 749/100000000) (ψ := 771483/1000000) 149 127
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t216 : ((-48705054741/1250000000000 : ℚ) : ℝ) ≤ stT149 216 := by
  have hc : ((-143163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48705054741/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-143163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c217 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-60187/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 179293/250000) (δ := 759/100000000) (ψ := 771483/1000000) 149 127
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t217 : ((-65375624649/1000000000000 : ℚ) : ℝ) ≤ stT149 217 := by
  have hc : ((-481521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65375624649/1000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-481521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c218 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-916261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17059/25000) (δ := 7583/1000000000) (ψ := 771483/1000000) 149 128
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t218 : ((-310302305973/5000000000000 : ℚ) : ℝ) ≤ stT149 218 := by
  have hc : ((-916311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-310302305973/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-916311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c219 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-458863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5118779/10000000) (δ := 7483/1000000000) (ψ := 771483/1000000) 149 128
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t219 : ((-155052476397/5000000000000 : ℚ) : ℝ) ≤ stT149 219 := by
  have hc : ((-458913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155052476397/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-458913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c220 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((100363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3421743/10000000) (δ := 381/50000000) (ψ := 771483/1000000) 149 128
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t220 : ((33823889631/2500000000000 : ℚ) : ℝ) ≤ stT149 220 := by
  have hc : ((50169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33823889631/2500000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((50169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c221 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((769363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1732381/10000000) (δ := 381/50000000) (ψ := 771483/1000000) 149 128
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t221 : ((16171728573/312500000000 : ℚ) : ℝ) ≤ stT149 221 := by
  have hc : ((769313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16171728573/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((769313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c222 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((499897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50693/10000000) (δ := 7483/1000000000) (ψ := 771483/1000000) 149 128
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t222 : ((2621031969/39062500000 : ℚ) : ℝ) ≤ stT149 222 := by
  have hc : ((15621/15625 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2621031969/39062500000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((15621/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c223 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((398227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1623471/10000000) (δ := 7483/1000000000) (ψ := 771483/1000000) 149 128
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t223 : ((133327785549/2500000000000 : ℚ) : ℝ) ≤ stT149 223 := by
  have hc : ((199101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133327785549/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((199101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c224 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((251991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 822537/2500000) (δ := 47/6250000) (ψ := 771483/1000000) 149 128
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t224 : ((168335134973/10000000000000 : ℚ) : ℝ) ≤ stT149 224 := by
  have hc : ((251941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168335134973/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((251941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c225 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-397663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1237353/2500000) (δ := 47/6250000) (ψ := 771483/1000000) 149 128
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t225 : ((-265142132571/10000000000000 : ℚ) : ℝ) ≤ stT149 225 := by
  have hc : ((-397713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265142132571/10000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-397713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c226 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-109633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3300641/5000000) (δ := 751/50000000) (ψ := 771483/1000000) 149 128
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t226 : ((-291724169387/5000000000000 : ℚ) : ℝ) ≤ stT149 226 := by
  have hc : ((-438557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291724169387/5000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-438557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c227 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-493869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298483/400000) (δ := 1907/250000000) (ψ := 771483/1000000) 149 129
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t227 : ((-40976162657/625000000000 : ℚ) : ℝ) ≤ stT149 227 := by
  have hc : ((-246947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40976162657/625000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-246947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c228 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-688261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2912357/5000000) (δ := 1907/250000000) (ψ := 771483/1000000) 149 129
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t228 : ((-455845661037/10000000000000 : ℚ) : ℝ) ≤ stT149 228 := by
  have hc : ((-688311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-455845661037/10000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-688311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c229 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-53401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -838901/2000000) (δ := 1907/250000000) (ψ := 771483/1000000) 149 129
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t229 : ((-17652457947/2500000000000 : ℚ) : ℝ) ≤ stT149 229 := by
  have hc : ((-26713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17652457947/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-26713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c230 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((516049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2571411/10000000) (δ := 941/125000000) (ψ := 771483/1000000) 149 129
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t230 : ((17011971031/500000000000 : ℚ) : ℝ) ≤ stT149 230 := by
  have hc : ((515999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17011971031/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((515999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c231 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((231967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -955357/10000000) (δ := 941/125000000) (ψ := 771483/1000000) 149 129
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t231 : ((305229390459/5000000000000 : ℚ) : ℝ) ≤ stT149 231 := by
  have hc : ((463909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305229390459/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((463909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c232 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((966009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326847/5000000) (δ := 941/125000000) (ψ := 771483/1000000) 149 129
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t232 : ((158545748547/2500000000000 : ℚ) : ℝ) ≤ stT149 232 := by
  have hc : ((965959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158545748547/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((965959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c233 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((309887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1127927/5000000) (δ := 1907/250000000) (ψ := 771483/1000000) 149 129
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t233 : ((101498551651/2500000000000 : ℚ) : ℝ) ≤ stT149 233 := by
  have hc : ((154931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101498551651/2500000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((154931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c234 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((3791/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3851159/10000000) (δ := 303/40000000) (ψ := 771483/1000000) 149 129
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t234 : ((247416677/125000000000 : ℚ) : ℝ) ≤ stT149 234 := by
  have hc : ((15139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247416677/125000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((15139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c235 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-284407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 169989/312500) (δ := 303/40000000) (ψ := 771483/1000000) 149 129
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t235 : ((-11596452633/312500000000 : ℚ) : ℝ) ≤ stT149 235 := by
  have hc : ((-17777/31250 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11596452633/312500000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-17777/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c236 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-189011/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1404279/2000000) (δ := 299/40000000) (ψ := 771483/1000000) 149 129
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t236 : ((-24608454969/400000000000 : ℚ) : ℝ) ≤ stT149 236 := by
  have hc : ((-189021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24608454969/400000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-189021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c237 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-14941/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3555763/5000000) (δ := 1527/200000000) (ψ := 771483/1000000) 149 130
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t237 : ((-31058345109/500000000000 : ℚ) : ℝ) ≤ stT149 237 := by
  have hc : ((-478137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31058345109/500000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-478137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c238 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-150589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1108623/2000000) (δ := 1507/200000000) (ψ := 771483/1000000) 149 130
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t238 : ((-48810247353/1250000000000 : ℚ) : ℝ) ≤ stT149 238 := by
  have hc : ((-301203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48810247353/1250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-301203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c239 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-10853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199063/500000) (δ := 1867/250000000) (ψ := 771483/1000000) 149 130
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t239 : ((-3518200833/2500000000000 : ℚ) : ℝ) ≤ stT149 239 := by
  have hc : ((-5439/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3518200833/2500000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-5439/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c240 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((112999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2425923/10000000) (δ := 1527/200000000) (ψ := 771483/1000000) 149 130
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t240 : ((72934060533/2000000000000 : ℚ) : ℝ) ≤ stT149 240 := by
  have hc : ((112989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72934060533/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((112989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c241 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((939089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219267/2500000) (δ := 1527/200000000) (ψ := 771483/1000000) 149 130
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t241 : ((151221901521/2500000000000 : ℚ) : ℝ) ≤ stT149 241 := by
  have hc : ((939039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151221901521/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((939039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c242 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((96479/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33269/500000) (δ := 1527/200000000) (ψ := 771483/1000000) 149 130
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t242 : ((3875987661/62500000000 : ℚ) : ℝ) ≤ stT149 242 := by
  have hc : ((48237/50000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3875987661/62500000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((48237/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c243 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((318351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1100729/5000000) (δ := 1507/200000000) (ψ := 771483/1000000) 149 130
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t243 : ((204206129/5000000000 : ℚ) : ℝ) ≤ stT149 243 := by
  have hc : ((159163/250000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204206129/5000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((159163/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c244 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((3911/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3731241/10000000) (δ := 1507/200000000) (ψ := 771483/1000000) 149 130
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t244 : ((625539791/125000000000 : ℚ) : ℝ) ≤ stT149 244 := by
  have hc : ((7817/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625539791/125000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((7817/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c245 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-126621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5254747/10000000) (δ := 1871/125000000) (ψ := 771483/1000000) 149 130
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t245 : ((-161806461159/5000000000000 : ℚ) : ℝ) ≤ stT149 245 := by
  have hc : ((-253267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161806461159/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-253267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c246 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-90781/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677207/1000000) (δ := 1867/250000000) (ψ := 771483/1000000) 149 130
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t246 : ((-28941532761/500000000000 : ℚ) : ℝ) ≤ stT149 246 := by
  have hc : ((-45393/50000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28941532761/500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-45393/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c247 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-61581/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1484947/2000000) (δ := 3771/500000000) (ψ := 771483/1000000) 149 131
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t247 : ((-62696087961/1000000000000 : ℚ) : ℝ) ≤ stT149 247 := by
  have hc : ((-492673/500000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62696087961/1000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-492673/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c248 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-715317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2959843/5000000) (δ := 3771/500000000) (ψ := 771483/1000000) 149 131
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t248 : ((-454258760367/10000000000000 : ℚ) : ℝ) ≤ stT149 248 := by
  have hc : ((-715367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454258760367/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-715367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c249 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-98103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4420709/10000000) (δ := 7461/1000000000) (ψ := 771483/1000000) 149 131
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t249 : ((-155465417/12500000000 : ℚ) : ℝ) ≤ stT149 249 := by
  have hc : ((-6133/31250 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155465417/12500000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-6133/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_c250 :
    |Real.cos (((149 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((9729/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -731923/2500000) (δ := 7561/1000000000) (ψ := 771483/1000000) 149 131
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st149_t250 : ((4921891301/200000000000 : ℚ) : ℝ) ≤ stT149 250 := by
  have hc : ((38911/100000 : ℚ) : ℝ)
      ≤ Real.cos (((149 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st149_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4921891301/200000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((38911/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st149_p1 : ((716827/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT149 (i+1) := by
  rw [Finset.sum_range_one]
  exact st149_t1

theorem st149_p2 : ((218867740787/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT149 (i+1))
      = (∑ i ∈ Finset.range 1, stT149 (i+1)) + stT149 2 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 1
    simpa using h
  have hprev := st149_p1
  have hstep := st149_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p3 : ((4799001792363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT149 (i+1))
      = (∑ i ∈ Finset.range 2, stT149 (i+1)) + stT149 3 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 2
    simpa using h
  have hprev := st149_p2
  have hstep := st149_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p4 : ((4829016792363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT149 (i+1))
      = (∑ i ∈ Finset.range 3, stT149 (i+1)) + stT149 4 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 3
    simpa using h
  have hprev := st149_p3
  have hstep := st149_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p5 : ((13963442919791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT149 (i+1))
      = (∑ i ∈ Finset.range 4, stT149 (i+1)) + stT149 5 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 4
    simpa using h
  have hprev := st149_p4
  have hstep := st149_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p6 : ((11222259709441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT149 (i+1))
      = (∑ i ∈ Finset.range 5, stT149 (i+1)) + stT149 6 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 5
    simpa using h
  have hprev := st149_p5
  have hstep := st149_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p7 : ((14963347560997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT149 (i+1))
      = (∑ i ∈ Finset.range 6, stT149 (i+1)) + stT149 7 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 6
    simpa using h
  have hprev := st149_p6
  have hstep := st149_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p8 : ((3255943684151/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT149 (i+1))
      = (∑ i ∈ Finset.range 7, stT149 (i+1)) + stT149 8 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 7
    simpa using h
  have hprev := st149_p7
  have hstep := st149_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p9 : ((1224530922259/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT149 (i+1))
      = (∑ i ∈ Finset.range 8, stT149 (i+1)) + stT149 9 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 8
    simpa using h
  have hprev := st149_p8
  have hstep := st149_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p10 : ((8226383480281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT149 (i+1))
      = (∑ i ∈ Finset.range 9, stT149 (i+1)) + stT149 10 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 9
    simpa using h
  have hprev := st149_p9
  have hstep := st149_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p11 : ((1628428842047/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT149 (i+1))
      = (∑ i ∈ Finset.range 10, stT149 (i+1)) + stT149 11 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 10
    simpa using h
  have hprev := st149_p10
  have hstep := st149_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p12 : ((539173789273/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT149 (i+1))
      = (∑ i ∈ Finset.range 11, stT149 (i+1)) + stT149 12 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 11
    simpa using h
  have hprev := st149_p11
  have hstep := st149_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p13 : ((16440323614019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT149 (i+1))
      = (∑ i ∈ Finset.range 12, stT149 (i+1)) + stT149 13 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 12
    simpa using h
  have hprev := st149_p12
  have hstep := st149_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p14 : ((13851336674789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT149 (i+1))
      = (∑ i ∈ Finset.range 13, stT149 (i+1)) + stT149 14 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 13
    simpa using h
  have hprev := st149_p13
  have hstep := st149_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p15 : ((15976152715533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT149 (i+1))
      = (∑ i ∈ Finset.range 14, stT149 (i+1)) + stT149 15 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 14
    simpa using h
  have hprev := st149_p14
  have hstep := st149_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p16 : ((14226392015629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT149 (i+1))
      = (∑ i ∈ Finset.range 15, stT149 (i+1)) + stT149 16 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 15
    simpa using h
  have hprev := st149_p15
  have hstep := st149_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p17 : ((16456480178713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT149 (i+1))
      = (∑ i ∈ Finset.range 16, stT149 (i+1)) + stT149 17 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 16
    simpa using h
  have hprev := st149_p16
  have hstep := st149_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p18 : ((14392741550603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT149 (i+1))
      = (∑ i ∈ Finset.range 17, stT149 (i+1)) + stT149 18 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 17
    simpa using h
  have hprev := st149_p17
  have hstep := st149_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p19 : ((13709717948369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT149 (i+1))
      = (∑ i ∈ Finset.range 18, stT149 (i+1)) + stT149 19 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 18
    simpa using h
  have hprev := st149_p18
  have hstep := st149_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p20 : ((15657251806957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT149 (i+1))
      = (∑ i ∈ Finset.range 19, stT149 (i+1)) + stT149 20 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 19
    simpa using h
  have hprev := st149_p19
  have hstep := st149_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p21 : ((17599711007123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT149 (i+1))
      = (∑ i ∈ Finset.range 20, stT149 (i+1)) + stT149 21 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 20
    simpa using h
  have hprev := st149_p20
  have hstep := st149_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p22 : ((9262979658133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT149 (i+1))
      = (∑ i ∈ Finset.range 21, stT149 (i+1)) + stT149 22 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 21
    simpa using h
  have hprev := st149_p21
  have hstep := st149_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p23 : ((1875340890893/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT149 (i+1))
      = (∑ i ∈ Finset.range 22, stT149 (i+1)) + stT149 23 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 22
    simpa using h
  have hprev := st149_p22
  have hstep := st149_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p24 : ((18857677540451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT149 (i+1))
      = (∑ i ∈ Finset.range 23, stT149 (i+1)) + stT149 24 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 23
    simpa using h
  have hprev := st149_p23
  have hstep := st149_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p25 : ((19355991540451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT149 (i+1))
      = (∑ i ∈ Finset.range 24, stT149 (i+1)) + stT149 25 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 24
    simpa using h
  have hprev := st149_p24
  have hstep := st149_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p26 : ((10303001111057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT149 (i+1))
      = (∑ i ∈ Finset.range 25, stT149 (i+1)) + stT149 26 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 25
    simpa using h
  have hprev := st149_p25
  have hstep := st149_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p27 : ((11242061848307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT149 (i+1))
      = (∑ i ∈ Finset.range 26, stT149 (i+1)) + stT149 27 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 26
    simpa using h
  have hprev := st149_p26
  have hstep := st149_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p28 : ((11997295193811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT149 (i+1))
      = (∑ i ∈ Finset.range 27, stT149 (i+1)) + stT149 28 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 27
    simpa using h
  have hprev := st149_p27
  have hstep := st149_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p29 : ((742395763827/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT149 (i+1))
      = (∑ i ∈ Finset.range 28, stT149 (i+1)) + stT149 29 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 28
    simpa using h
  have hprev := st149_p28
  have hstep := st149_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p30 : ((1373195786517/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT149 (i+1))
      = (∑ i ∈ Finset.range 29, stT149 (i+1)) + stT149 30 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 29
    simpa using h
  have hprev := st149_p29
  have hstep := st149_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p31 : ((10649248894447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT149 (i+1))
      = (∑ i ∈ Finset.range 30, stT149 (i+1)) + stT149 31 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 30
    simpa using h
  have hprev := st149_p30
  have hstep := st149_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p32 : ((2865658125621/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT149 (i+1))
      = (∑ i ∈ Finset.range 31, stT149 (i+1)) + stT149 32 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 31
    simpa using h
  have hprev := st149_p31
  have hstep := st149_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p33 : ((365580295251/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT149 (i+1))
      = (∑ i ∈ Finset.range 32, stT149 (i+1)) + stT149 33 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 32
    simpa using h
  have hprev := st149_p32
  have hstep := st149_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p34 : ((10841079020511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT149 (i+1))
      = (∑ i ∈ Finset.range 33, stT149 (i+1)) + stT149 34 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 33
    simpa using h
  have hprev := st149_p33
  have hstep := st149_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p35 : ((446274528249/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT149 (i+1))
      = (∑ i ∈ Finset.range 34, stT149 (i+1)) + stT149 35 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 34
    simpa using h
  have hprev := st149_p34
  have hstep := st149_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p36 : ((291904804129/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT149 (i+1))
      = (∑ i ∈ Finset.range 35, stT149 (i+1)) + stT149 36 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 35
    simpa using h
  have hprev := st149_p35
  have hstep := st149_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p37 : ((13568642431/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT149 (i+1))
      = (∑ i ∈ Finset.range 36, stT149 (i+1)) + stT149 37 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 36
    simpa using h
  have hprev := st149_p36
  have hstep := st149_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p38 : ((11374842453977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT149 (i+1))
      = (∑ i ∈ Finset.range 37, stT149 (i+1)) + stT149 38 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 37
    simpa using h
  have hprev := st149_p37
  have hstep := st149_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p39 : ((2850280269117/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT149 (i+1))
      = (∑ i ∈ Finset.range 38, stT149 (i+1)) + stT149 39 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 38
    simpa using h
  have hprev := st149_p38
  have hstep := st149_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p40 : ((5457050901983/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT149 (i+1))
      = (∑ i ∈ Finset.range 39, stT149 (i+1)) + stT149 40 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 39
    simpa using h
  have hprev := st149_p39
  have hstep := st149_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p41 : ((11642213266369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT149 (i+1))
      = (∑ i ∈ Finset.range 40, stT149 (i+1)) + stT149 41 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 40
    simpa using h
  have hprev := st149_p40
  have hstep := st149_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p42 : ((10873087969069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT149 (i+1))
      = (∑ i ∈ Finset.range 41, stT149 (i+1)) + stT149 42 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 41
    simpa using h
  have hprev := st149_p41
  have hstep := st149_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p43 : ((11561661396149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT149 (i+1))
      = (∑ i ∈ Finset.range 42, stT149 (i+1)) + stT149 43 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 42
    simpa using h
  have hprev := st149_p42
  have hstep := st149_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p44 : ((21997535004307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT149 (i+1))
      = (∑ i ∈ Finset.range 43, stT149 (i+1)) + stT149 44 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 43
    simpa using h
  have hprev := st149_p43
  have hstep := st149_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p45 : ((5720804646073/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT149 (i+1))
      = (∑ i ∈ Finset.range 44, stT149 (i+1)) + stT149 45 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 44
    simpa using h
  have hprev := st149_p44
  have hstep := st149_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p46 : ((5543101649993/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT149 (i+1))
      = (∑ i ∈ Finset.range 45, stT149 (i+1)) + stT149 46 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 45
    simpa using h
  have hprev := st149_p45
  have hstep := st149_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p47 : ((11396908664827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT149 (i+1))
      = (∑ i ∈ Finset.range 46, stT149 (i+1)) + stT149 47 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 46
    simpa using h
  have hprev := st149_p46
  have hstep := st149_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p48 : ((11086360544923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT149 (i+1))
      = (∑ i ∈ Finset.range 47, stT149 (i+1)) + stT149 48 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 47
    simpa using h
  have hprev := st149_p47
  have hstep := st149_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p49 : ((357424433379/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT149 (i+1))
      = (∑ i ∈ Finset.range 48, stT149 (i+1)) + stT149 49 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 48
    simpa using h
  have hprev := st149_p48
  have hstep := st149_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p50 : ((2753040210269/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT149 (i+1))
      = (∑ i ∈ Finset.range 49, stT149 (i+1)) + stT149 50 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 49
    simpa using h
  have hprev := st149_p49
  have hstep := st149_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p51 : ((2882959238879/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT149 (i+1))
      = (∑ i ∈ Finset.range 50, stT149 (i+1)) + stT149 51 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 50
    simpa using h
  have hprev := st149_p50
  have hstep := st149_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p52 : ((10918716896139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT149 (i+1))
      = (∑ i ∈ Finset.range 51, stT149 (i+1)) + stT149 52 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 51
    simpa using h
  have hprev := st149_p51
  have hstep := st149_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p53 : ((23188133928903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT149 (i+1))
      = (∑ i ∈ Finset.range 52, stT149 (i+1)) + stT149 53 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 52
    simpa using h
  have hprev := st149_p52
  have hstep := st149_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p54 : ((21847756452087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT149 (i+1))
      = (∑ i ∈ Finset.range 53, stT149 (i+1)) + stT149 54 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 53
    simpa using h
  have hprev := st149_p53
  have hstep := st149_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p55 : ((22974502927669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT149 (i+1))
      = (∑ i ∈ Finset.range 54, stT149 (i+1)) + stT149 55 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 54
    simpa using h
  have hprev := st149_p54
  have hstep := st149_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p56 : ((22295993048419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT149 (i+1))
      = (∑ i ∈ Finset.range 55, stT149 (i+1)) + stT149 56 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 55
    simpa using h
  have hprev := st149_p55
  have hstep := st149_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p57 : ((22333220344811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT149 (i+1))
      = (∑ i ∈ Finset.range 56, stT149 (i+1)) + stT149 57 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 56
    simpa using h
  have hprev := st149_p56
  have hstep := st149_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p58 : ((22987929811979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT149 (i+1))
      = (∑ i ∈ Finset.range 57, stT149 (i+1)) + stT149 58 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 57
    simpa using h
  have hprev := st149_p57
  have hstep := st149_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p59 : ((21817978552139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT149 (i+1))
      = (∑ i ∈ Finset.range 58, stT149 (i+1)) + stT149 59 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 58
    simpa using h
  have hprev := st149_p58
  have hstep := st149_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p60 : ((23087322582759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT149 (i+1))
      = (∑ i ∈ Finset.range 59, stT149 (i+1)) + stT149 60 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 59
    simpa using h
  have hprev := st149_p59
  have hstep := st149_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p61 : ((2781711371457/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT149 (i+1))
      = (∑ i ∈ Finset.range 60, stT149 (i+1)) + stT149 61 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 60
    simpa using h
  have hprev := st149_p60
  have hstep := st149_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p62 : ((222411458919/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT149 (i+1))
      = (∑ i ∈ Finset.range 61, stT149 (i+1)) + stT149 62 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 61
    simpa using h
  have hprev := st149_p61
  have hstep := st149_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p63 : ((23115741423409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT149 (i+1))
      = (∑ i ∈ Finset.range 62, stT149 (i+1)) + stT149 63 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 62
    simpa using h
  have hprev := st149_p62
  have hstep := st149_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p64 : ((10932860836697/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT149 (i+1))
      = (∑ i ∈ Finset.range 63, stT149 (i+1)) + stT149 64 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 63
    simpa using h
  have hprev := st149_p63
  have hstep := st149_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p65 : ((22709010032101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT149 (i+1))
      = (∑ i ∈ Finset.range 64, stT149 (i+1)) + stT149 65 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 64
    simpa using h
  have hprev := st149_p64
  have hstep := st149_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p66 : ((4571032767361/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT149 (i+1))
      = (∑ i ∈ Finset.range 65, stT149 (i+1)) + stT149 66 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 65
    simpa using h
  have hprev := st149_p65
  have hstep := st149_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p67 : ((2181407811713/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT149 (i+1))
      = (∑ i ∈ Finset.range 66, stT149 (i+1)) + stT149 67 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 66
    simpa using h
  have hprev := st149_p66
  have hstep := st149_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p68 : ((11469336018961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT149 (i+1))
      = (∑ i ∈ Finset.range 67, stT149 (i+1)) + stT149 68 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 67
    simpa using h
  have hprev := st149_p67
  have hstep := st149_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p69 : ((11337320841021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT149 (i+1))
      = (∑ i ∈ Finset.range 68, stT149 (i+1)) + stT149 69 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 68
    simpa using h
  have hprev := st149_p68
  have hstep := st149_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p70 : ((10918443276139/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT149 (i+1))
      = (∑ i ∈ Finset.range 69, stT149 (i+1)) + stT149 70 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 69
    simpa using h
  have hprev := st149_p69
  have hstep := st149_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p71 : ((11495646083299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT149 (i+1))
      = (∑ i ∈ Finset.range 70, stT149 (i+1)) + stT149 71 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 70
    simpa using h
  have hprev := st149_p70
  have hstep := st149_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p72 : ((11333191150379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT149 (i+1))
      = (∑ i ∈ Finset.range 71, stT149 (i+1)) + stT149 72 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 71
    simpa using h
  have hprev := st149_p71
  have hstep := st149_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p73 : ((10910464670249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT149 (i+1))
      = (∑ i ∈ Finset.range 72, stT149 (i+1)) + stT149 73 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 72
    simpa using h
  have hprev := st149_p72
  have hstep := st149_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p74 : ((11456296557479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT149 (i+1))
      = (∑ i ∈ Finset.range 73, stT149 (i+1)) + stT149 74 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 73
    simpa using h
  have hprev := st149_p73
  have hstep := st149_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p75 : ((4564384505667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT149 (i+1))
      = (∑ i ∈ Finset.range 74, stT149 (i+1)) + stT149 75 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 74
    simpa using h
  have hprev := st149_p74
  have hstep := st149_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p76 : ((10902548895011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT149 (i+1))
      = (∑ i ∈ Finset.range 75, stT149 (i+1)) + stT149 76 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 75
    simpa using h
  have hprev := st149_p75
  have hstep := st149_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p77 : ((1416710674777/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT149 (i+1))
      = (∑ i ∈ Finset.range 76, stT149 (i+1)) + stT149 77 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 76
    simpa using h
  have hprev := st149_p76
  have hstep := st149_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p78 : ((23066977392103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT149 (i+1))
      = (∑ i ∈ Finset.range 77, stT149 (i+1)) + stT149 78 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 77
    simpa using h
  have hprev := st149_p77
  have hstep := st149_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p79 : ((4388492412379/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT149 (i+1))
      = (∑ i ∈ Finset.range 78, stT149 (i+1)) + stT149 79 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 78
    simpa using h
  have hprev := st149_p78
  have hstep := st149_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p80 : ((5560158409191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT149 (i+1))
      = (∑ i ∈ Finset.range 79, stT149 (i+1)) + stT149 80 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 79
    simpa using h
  have hprev := st149_p79
  have hstep := st149_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p81 : ((2318772909761/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT149 (i+1))
      = (∑ i ∈ Finset.range 80, stT149 (i+1)) + stT149 81 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 80
    simpa using h
  have hprev := st149_p80
  have hstep := st149_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p82 : ((11194824379469/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT149 (i+1))
      = (∑ i ∈ Finset.range 81, stT149 (i+1)) + stT149 82 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 81
    simpa using h
  have hprev := st149_p81
  have hstep := st149_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p83 : ((21836701218901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT149 (i+1))
      = (∑ i ∈ Finset.range 82, stT149 (i+1)) + stT149 83 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 82
    simpa using h
  have hprev := st149_p82
  have hstep := st149_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p84 : ((22874307218299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT149 (i+1))
      = (∑ i ∈ Finset.range 83, stT149 (i+1)) + stT149 84 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 83
    simpa using h
  have hprev := st149_p83
  have hstep := st149_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p85 : ((23005929738499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT149 (i+1))
      = (∑ i ∈ Finset.range 84, stT149 (i+1)) + stT149 85 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 84
    simpa using h
  have hprev := st149_p84
  have hstep := st149_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p86 : ((21928906515379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT149 (i+1))
      = (∑ i ∈ Finset.range 85, stT149 (i+1)) + stT149 86 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 85
    simpa using h
  have hprev := st149_p85
  have hstep := st149_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p87 : ((22143933586547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT149 (i+1))
      = (∑ i ∈ Finset.range 86, stT149 (i+1)) + stT149 87 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 86
    simpa using h
  have hprev := st149_p86
  have hstep := st149_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p88 : ((5787737860637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT149 (i+1))
      = (∑ i ∈ Finset.range 87, stT149 (i+1)) + stT149 88 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 87
    simpa using h
  have hprev := st149_p87
  have hstep := st149_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p89 : ((11346401143491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT149 (i+1))
      = (∑ i ∈ Finset.range 88, stT149 (i+1)) + stT149 89 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 88
    simpa using h
  have hprev := st149_p88
  have hstep := st149_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p90 : ((2723642889423/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT149 (i+1))
      = (∑ i ∈ Finset.range 89, stT149 (i+1)) + stT149 90 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 89
    simpa using h
  have hprev := st149_p89
  have hstep := st149_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p91 : ((5598808679271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT149 (i+1))
      = (∑ i ∈ Finset.range 90, stT149 (i+1)) + stT149 91 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 90
    simpa using h
  have hprev := st149_p90
  have hstep := st149_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p92 : ((1450603597413/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT149 (i+1))
      = (∑ i ∈ Finset.range 91, stT149 (i+1)) + stT149 92 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 91
    simpa using h
  have hprev := st149_p91
  have hstep := st149_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p93 : ((2816297546877/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT149 (i+1))
      = (∑ i ∈ Finset.range 92, stT149 (i+1)) + stT149 93 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 92
    simpa using h
  have hprev := st149_p92
  have hstep := st149_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p94 : ((10883291236389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT149 (i+1))
      = (∑ i ∈ Finset.range 93, stT149 (i+1)) + stT149 94 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 93
    simpa using h
  have hprev := st149_p93
  have hstep := st149_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p95 : ((2246056835567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT149 (i+1))
      = (∑ i ∈ Finset.range 94, stT149 (i+1)) + stT149 95 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 94
    simpa using h
  have hprev := st149_p94
  have hstep := st149_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p96 : ((2321943606799/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT149 (i+1))
      = (∑ i ∈ Finset.range 95, stT149 (i+1)) + stT149 96 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 95
    simpa using h
  have hprev := st149_p95
  have hstep := st149_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p97 : ((112804562321/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT149 (i+1))
      = (∑ i ∈ Finset.range 96, stT149 (i+1)) + stT149 97 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 96
    simpa using h
  have hprev := st149_p96
  have hstep := st149_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p98 : ((10882374127707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT149 (i+1))
      = (∑ i ∈ Finset.range 97, stT149 (i+1)) + stT149 98 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 97
    simpa using h
  have hprev := st149_p97
  have hstep := st149_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p99 : ((22336301741907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT149 (i+1))
      = (∑ i ∈ Finset.range 98, stT149 (i+1)) + stT149 99 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 98
    simpa using h
  have hprev := st149_p98
  have hstep := st149_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p100 : ((5799552969999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT149 (i+1))
      = (∑ i ∈ Finset.range 99, stT149 (i+1)) + stT149 100 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 99
    simpa using h
  have hprev := st149_p99
  have hstep := st149_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p101 : ((11385601133857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT149 (i+1))
      = (∑ i ∈ Finset.range 100, stT149 (i+1)) + stT149 101 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 100
    simpa using h
  have hprev := st149_p100
  have hstep := st149_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p102 : ((10918955768159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT149 (i+1))
      = (∑ i ∈ Finset.range 101, stT149 (i+1)) + stT149 102 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 101
    simpa using h
  have hprev := st149_p101
  have hstep := st149_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p103 : ((11028147957281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT149 (i+1))
      = (∑ i ∈ Finset.range 102, stT149 (i+1)) + stT149 103 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 102
    simpa using h
  have hprev := st149_p102
  have hstep := st149_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p104 : ((11516323336511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT149 (i+1))
      = (∑ i ∈ Finset.range 103, stT149 (i+1)) + stT149 104 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 103
    simpa using h
  have hprev := st149_p103
  have hstep := st149_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p105 : ((11541939247661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT149 (i+1))
      = (∑ i ∈ Finset.range 104, stT149 (i+1)) + stT149 105 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 104
    simpa using h
  have hprev := st149_p104
  have hstep := st149_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p106 : ((345845216461/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT149 (i+1))
      = (∑ i ∈ Finset.range 105, stT149 (i+1)) + stT149 106 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 105
    simpa using h
  have hprev := st149_p105
  have hstep := st149_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p107 : ((10886494290947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT149 (i+1))
      = (∑ i ∈ Finset.range 106, stT149 (i+1)) + stT149 107 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 106
    simpa using h
  have hprev := st149_p106
  have hstep := st149_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p108 : ((11292178890947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT149 (i+1))
      = (∑ i ∈ Finset.range 107, stT149 (i+1)) + stT149 108 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 107
    simpa using h
  have hprev := st149_p107
  have hstep := st149_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p109 : ((290595665559/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT149 (i+1))
      = (∑ i ∈ Finset.range 108, stT149 (i+1)) + stT149 109 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 108
    simpa using h
  have hprev := st149_p108
  have hstep := st149_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p110 : ((11356304927283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT149 (i+1))
      = (∑ i ∈ Finset.range 109, stT149 (i+1)) + stT149 110 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 109
    simpa using h
  have hprev := st149_p109
  have hstep := st149_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p111 : ((10914397843959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT149 (i+1))
      = (∑ i ∈ Finset.range 110, stT149 (i+1)) + stT149 111 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 110
    simpa using h
  have hprev := st149_p110
  have hstep := st149_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p112 : ((21959562866119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT149 (i+1))
      = (∑ i ∈ Finset.range 111, stT149 (i+1)) + stT149 112 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 111
    simpa using h
  have hprev := st149_p111
  have hstep := st149_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p113 : ((22894810697879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT149 (i+1))
      = (∑ i ∈ Finset.range 112, stT149 (i+1)) + stT149 113 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 112
    simpa using h
  have hprev := st149_p112
  have hstep := st149_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p114 : ((5807370856421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT149 (i+1))
      = (∑ i ∈ Finset.range 113, stT149 (i+1)) + stT149 114 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 113
    simpa using h
  have hprev := st149_p113
  have hstep := st149_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p115 : ((22478670497399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT149 (i+1))
      = (∑ i ∈ Finset.range 114, stT149 (i+1)) + stT149 115 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 114
    simpa using h
  have hprev := st149_p114
  have hstep := st149_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p116 : ((21742354811227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT149 (i+1))
      = (∑ i ∈ Finset.range 115, stT149 (i+1)) + stT149 116 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 115
    simpa using h
  have hprev := st149_p115
  have hstep := st149_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p117 : ((22070833359227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT149 (i+1))
      = (∑ i ∈ Finset.range 116, stT149 (i+1)) + stT149 117 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 116
    simpa using h
  have hprev := st149_p116
  have hstep := st149_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p118 : ((22989672077237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT149 (i+1))
      = (∑ i ∈ Finset.range 117, stT149 (i+1)) + stT149 118 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 117
    simpa using h
  have hprev := st149_p117
  have hstep := st149_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p119 : ((23218929080057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT149 (i+1))
      = (∑ i ∈ Finset.range 118, stT149 (i+1)) + stT149 119 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 118
    simpa using h
  have hprev := st149_p118
  have hstep := st149_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p120 : ((898147064949/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT149 (i+1))
      = (∑ i ∈ Finset.range 119, stT149 (i+1)) + stT149 120 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 119
    simpa using h
  have hprev := st149_p119
  have hstep := st149_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p121 : ((5433833001609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT149 (i+1))
      = (∑ i ∈ Finset.range 120, stT149 (i+1)) + stT149 121 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 120
    simpa using h
  have hprev := st149_p120
  have hstep := st149_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p122 : ((22016060578211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT149 (i+1))
      = (∑ i ∈ Finset.range 121, stT149 (i+1)) + stT149 122 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 121
    simpa using h
  have hprev := st149_p121
  have hstep := st149_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p123 : ((22916993816307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT149 (i+1))
      = (∑ i ∈ Finset.range 122, stT149 (i+1)) + stT149 123 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 122
    simpa using h
  have hprev := st149_p122
  have hstep := st149_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p124 : ((23269511228529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT149 (i+1))
      = (∑ i ∈ Finset.range 123, stT149 (i+1)) + stT149 124 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 123
    simpa using h
  have hprev := st149_p123
  have hstep := st149_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p125 : ((4526400997649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT149 (i+1))
      = (∑ i ∈ Finset.range 124, stT149 (i+1)) + stT149 125 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 124
    simpa using h
  have hprev := st149_p124
  have hstep := st149_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p126 : ((5453714059027/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT149 (i+1))
      = (∑ i ∈ Finset.range 125, stT149 (i+1)) + stT149 126 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 125
    simpa using h
  have hprev := st149_p125
  have hstep := st149_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p127 : ((1364361514131/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT149 (i+1))
      = (∑ i ∈ Finset.range 126, stT149 (i+1)) + stT149 127 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 126
    simpa using h
  have hprev := st149_p126
  have hstep := st149_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p128 : ((22648826453099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT149 (i+1))
      = (∑ i ∈ Finset.range 127, stT149 (i+1)) + stT149 128 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 127
    simpa using h
  have hprev := st149_p127
  have hstep := st149_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p129 : ((23278249592699/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT149 (i+1))
      = (∑ i ∈ Finset.range 128, stT149 (i+1)) + stT149 129 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 128
    simpa using h
  have hprev := st149_p128
  have hstep := st149_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p130 : ((11487067761931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT149 (i+1))
      = (∑ i ∈ Finset.range 129, stT149 (i+1)) + stT149 130 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 129
    simpa using h
  have hprev := st149_p129
  have hstep := st149_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p131 : ((11051420974831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT149 (i+1))
      = (∑ i ∈ Finset.range 130, stT149 (i+1)) + stT149 131 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 130
    simpa using h
  have hprev := st149_p130
  have hstep := st149_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p132 : ((21675850865987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT149 (i+1))
      = (∑ i ∈ Finset.range 131, stT149 (i+1)) + stT149 132 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 131
    simpa using h
  have hprev := st149_p131
  have hstep := st149_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p133 : ((22173854109521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT149 (i+1))
      = (∑ i ∈ Finset.range 132, stT149 (i+1)) + stT149 133 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 132
    simpa using h
  have hprev := st149_p132
  have hstep := st149_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p134 : ((23027033470757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT149 (i+1))
      = (∑ i ∈ Finset.range 133, stT149 (i+1)) + stT149 134 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 133
    simpa using h
  have hprev := st149_p133
  have hstep := st149_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p135 : ((23286128880561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT149 (i+1))
      = (∑ i ∈ Finset.range 134, stT149 (i+1)) + stT149 135 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 134
    simpa using h
  have hprev := st149_p134
  have hstep := st149_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p136 : ((11337337744779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT149 (i+1))
      = (∑ i ∈ Finset.range 135, stT149 (i+1)) + stT149 136 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 135
    simpa using h
  have hprev := st149_p135
  have hstep := st149_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p137 : ((2732775512403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT149 (i+1))
      = (∑ i ∈ Finset.range 136, stT149 (i+1)) + stT149 137 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 136
    simpa using h
  have hprev := st149_p136
  have hstep := st149_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p138 : ((678624543339/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT149 (i+1))
      = (∑ i ∈ Finset.range 137, stT149 (i+1)) + stT149 138 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 137
    simpa using h
  have hprev := st149_p137
  have hstep := st149_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p139 : ((559551558353/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT149 (i+1))
      = (∑ i ∈ Finset.range 138, stT149 (i+1)) + stT149 139 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 138
    simpa using h
  have hprev := st149_p138
  have hstep := st149_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p140 : ((2895034172011/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT149 (i+1))
      = (∑ i ∈ Finset.range 139, stT149 (i+1)) + stT149 140 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 139
    simpa using h
  have hprev := st149_p139
  have hstep := st149_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p141 : ((23252466172511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT149 (i+1))
      = (∑ i ∈ Finset.range 140, stT149 (i+1)) + stT149 141 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 140
    simpa using h
  have hprev := st149_p140
  have hstep := st149_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p142 : ((22573121489687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT149 (i+1))
      = (∑ i ∈ Finset.range 141, stT149 (i+1)) + stT149 142 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 141
    simpa using h
  have hprev := st149_p141
  have hstep := st149_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p143 : ((4361773460917/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT149 (i+1))
      = (∑ i ∈ Finset.range 142, stT149 (i+1)) + stT149 143 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 142
    simpa using h
  have hprev := st149_p142
  have hstep := st149_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p144 : ((21713718061799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT149 (i+1))
      = (∑ i ∈ Finset.range 143, stT149 (i+1)) + stT149 144 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 143
    simpa using h
  have hprev := st149_p143
  have hstep := st149_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p145 : ((894910454939/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT149 (i+1))
      = (∑ i ∈ Finset.range 144, stT149 (i+1)) + stT149 145 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 144
    simpa using h
  have hprev := st149_p144
  have hstep := st149_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p146 : ((4628861213197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT149 (i+1))
      = (∑ i ∈ Finset.range 145, stT149 (i+1)) + stT149 146 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 145
    simpa using h
  have hprev := st149_p145
  have hstep := st149_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p147 : ((23294923536589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT149 (i+1))
      = (∑ i ∈ Finset.range 146, stT149 (i+1)) + stT149 147 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 146
    simpa using h
  have hprev := st149_p146
  have hstep := st149_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p148 : ((11345131596297/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT149 (i+1))
      = (∑ i ∈ Finset.range 147, stT149 (i+1)) + stT149 148 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 147
    simpa using h
  have hprev := st149_p147
  have hstep := st149_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p149 : ((10949164001417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT149 (i+1))
      = (∑ i ∈ Finset.range 148, stT149 (i+1)) + stT149 149 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 148
    simpa using h
  have hprev := st149_p148
  have hstep := st149_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p150 : ((10822628195339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT149 (i+1))
      = (∑ i ∈ Finset.range 149, stT149 (i+1)) + stT149 150 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 149
    simpa using h
  have hprev := st149_p149
  have hstep := st149_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p151 : ((11076862076843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT149 (i+1))
      = (∑ i ∈ Finset.range 150, stT149 (i+1)) + stT149 151 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 150
    simpa using h
  have hprev := st149_p150
  have hstep := st149_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p152 : ((358776186679/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT149 (i+1))
      = (∑ i ∈ Finset.range 151, stT149 (i+1)) + stT149 152 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 151
    simpa using h
  have hprev := st149_p151
  have hstep := st149_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p153 : ((5838382955851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT149 (i+1))
      = (∑ i ∈ Finset.range 152, stT149 (i+1)) + stT149 153 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 152
    simpa using h
  have hprev := st149_p152
  have hstep := st149_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p154 : ((1149620998703/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT149 (i+1))
      = (∑ i ∈ Finset.range 153, stT149 (i+1)) + stT149 154 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 153
    simpa using h
  have hprev := st149_p153
  have hstep := st149_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p155 : ((1109860966127/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT149 (i+1))
      = (∑ i ∈ Finset.range 154, stT149 (i+1)) + stT149 155 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 154
    simpa using h
  have hprev := st149_p154
  have hstep := st149_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p156 : ((21648875513819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT149 (i+1))
      = (∑ i ∈ Finset.range 155, stT149 (i+1)) + stT149 156 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 155
    simpa using h
  have hprev := st149_p155
  have hstep := st149_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p157 : ((21805597257811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT149 (i+1))
      = (∑ i ∈ Finset.range 156, stT149 (i+1)) + stT149 157 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 156
    simpa using h
  have hprev := st149_p156
  have hstep := st149_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p158 : ((22529663914677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT149 (i+1))
      = (∑ i ∈ Finset.range 157, stT149 (i+1)) + stT149 158 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 157
    simpa using h
  have hprev := st149_p157
  have hstep := st149_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p159 : ((23220585806897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT149 (i+1))
      = (∑ i ∈ Finset.range 158, stT149 (i+1)) + stT149 159 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 158
    simpa using h
  have hprev := st149_p158
  have hstep := st149_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p160 : ((23318021855009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT149 (i+1))
      = (∑ i ∈ Finset.range 159, stT149 (i+1)) + stT149 160 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 159
    simpa using h
  have hprev := st149_p159
  have hstep := st149_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p161 : ((2843754274733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT149 (i+1))
      = (∑ i ∈ Finset.range 160, stT149 (i+1)) + stT149 161 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 160
    simpa using h
  have hprev := st149_p160
  have hstep := st149_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p162 : ((10986963574007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT149 (i+1))
      = (∑ i ∈ Finset.range 161, stT149 (i+1)) + stT149 162 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 161
    simpa using h
  have hprev := st149_p161
  have hstep := st149_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p163 : ((21600215309911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT149 (i+1))
      = (∑ i ∈ Finset.range 162, stT149 (i+1)) + stT149 163 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 162
    simpa using h
  have hprev := st149_p162
  have hstep := st149_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p164 : ((4382858895027/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT149 (i+1))
      = (∑ i ∈ Finset.range 163, stT149 (i+1)) + stT149 164 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 163
    simpa using h
  have hprev := st149_p163
  have hstep := st149_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p165 : ((22668352308923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT149 (i+1))
      = (∑ i ∈ Finset.range 164, stT149 (i+1)) + stT149 165 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 164
    simpa using h
  have hprev := st149_p164
  have hstep := st149_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p166 : ((23286537156323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT149 (i+1))
      = (∑ i ∈ Finset.range 165, stT149 (i+1)) + stT149 166 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 165
    simpa using h
  have hprev := st149_p165
  have hstep := st149_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p167 : ((11653546882159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT149 (i+1))
      = (∑ i ∈ Finset.range 166, stT149 (i+1)) + stT149 167 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 166
    simpa using h
  have hprev := st149_p166
  have hstep := st149_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p168 : ((4544179183847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT149 (i+1))
      = (∑ i ∈ Finset.range 167, stT149 (i+1)) + stT149 168 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 167
    simpa using h
  have hprev := st149_p167
  have hstep := st149_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p169 : ((5490891423009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT149 (i+1))
      = (∑ i ∈ Finset.range 168, stT149 (i+1)) + stT149 169 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 168
    simpa using h
  have hprev := st149_p168
  have hstep := st149_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p170 : ((1349097074151/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT149 (i+1))
      = (∑ i ∈ Finset.range 169, stT149 (i+1)) + stT149 170 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 169
    simpa using h
  have hprev := st149_p169
  have hstep := st149_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p171 : ((10926942718163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT149 (i+1))
      = (∑ i ∈ Finset.range 170, stT149 (i+1)) + stT149 171 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 170
    simpa using h
  have hprev := st149_p170
  have hstep := st149_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p172 : ((11285908320677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT149 (i+1))
      = (∑ i ∈ Finset.range 171, stT149 (i+1)) + stT149 172 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 171
    simpa using h
  have hprev := st149_p171
  have hstep := st149_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p173 : ((23231436105929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT149 (i+1))
      = (∑ i ∈ Finset.range 172, stT149 (i+1)) + stT149 173 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 172
    simpa using h
  have hprev := st149_p172
  have hstep := st149_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p174 : ((23375803740461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT149 (i+1))
      = (∑ i ∈ Finset.range 173, stT149 (i+1)) + stT149 174 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 173
    simpa using h
  have hprev := st149_p173
  have hstep := st149_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p175 : ((2291096863571/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT149 (i+1))
      = (∑ i ∈ Finset.range 174, stT149 (i+1)) + stT149 175 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 174
    simpa using h
  have hprev := st149_p174
  have hstep := st149_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p176 : ((11079244575353/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT149 (i+1))
      = (∑ i ∈ Finset.range 175, stT149 (i+1)) + stT149 176 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 175
    simpa using h
  have hprev := st149_p175
  have hstep := st149_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p177 : ((10813274284403/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT149 (i+1))
      = (∑ i ∈ Finset.range 176, stT149 (i+1)) + stT149 177 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 176
    simpa using h
  have hprev := st149_p176
  have hstep := st149_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p178 : ((1083320956041/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT149 (i+1))
      = (∑ i ∈ Finset.range 177, stT149 (i+1)) + stT149 178 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 177
    simpa using h
  have hprev := st149_p177
  have hstep := st149_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p179 : ((4449251204667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT149 (i+1))
      = (∑ i ∈ Finset.range 178, stT149 (i+1)) + stT149 179 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 178
    simpa using h
  have hprev := st149_p178
  have hstep := st149_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p180 : ((4596700610329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT149 (i+1))
      = (∑ i ∈ Finset.range 179, stT149 (i+1)) + stT149 180 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 179
    simpa using h
  have hprev := st149_p179
  have hstep := st149_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p181 : ((4680388081789/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT149 (i+1))
      = (∑ i ∈ Finset.range 180, stT149 (i+1)) + stT149 181 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 180
    simpa using h
  have hprev := st149_p180
  have hstep := st149_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p182 : ((4647606004039/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT149 (i+1))
      = (∑ i ∈ Finset.range 181, stT149 (i+1)) + stT149 182 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 181
    simpa using h
  have hprev := st149_p181
  have hstep := st149_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p183 : ((22600723078891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT149 (i+1))
      = (∑ i ∈ Finset.range 182, stT149 (i+1)) + stT149 183 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 182
    simpa using h
  have hprev := st149_p182
  have hstep := st149_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p184 : ((21892300392181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT149 (i+1))
      = (∑ i ∈ Finset.range 183, stT149 (i+1)) + stT149 184 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 183
    simpa using h
  have hprev := st149_p183
  have hstep := st149_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p185 : ((21551034175201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT149 (i+1))
      = (∑ i ∈ Finset.range 184, stT149 (i+1)) + stT149 185 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 184
    simpa using h
  have hprev := st149_p184
  have hstep := st149_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p186 : ((5445514181589/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT149 (i+1))
      = (∑ i ∈ Finset.range 185, stT149 (i+1)) + stT149 186 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 185
    simpa using h
  have hprev := st149_p185
  have hstep := st149_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p187 : ((5610021679163/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT149 (i+1))
      = (∑ i ∈ Finset.range 186, stT149 (i+1)) + stT149 187 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 186
    simpa using h
  have hprev := st149_p186
  have hstep := st149_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p188 : ((2890849448251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT149 (i+1))
      = (∑ i ∈ Finset.range 187, stT149 (i+1)) + stT149 188 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 187
    simpa using h
  have hprev := st149_p187
  have hstep := st149_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p189 : ((2929321665751/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT149 (i+1))
      = (∑ i ∈ Finset.range 188, stT149 (i+1)) + stT149 189 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 188
    simpa using h
  have hprev := st149_p188
  have hstep := st149_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p190 : ((23186231666753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT149 (i+1))
      = (∑ i ∈ Finset.range 189, stT149 (i+1)) + stT149 190 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 189
    simpa using h
  have hprev := st149_p189
  have hstep := st149_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p191 : ((176025996501/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT149 (i+1))
      = (∑ i ∈ Finset.range 190, stT149 (i+1)) + stT149 191 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 190
    simpa using h
  have hprev := st149_p190
  have hstep := st149_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p192 : ((682831781149/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT149 (i+1))
      = (∑ i ∈ Finset.range 191, stT149 (i+1)) + stT149 192 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 191
    simpa using h
  have hprev := st149_p191
  have hstep := st149_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p193 : ((2691537405679/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT149 (i+1))
      = (∑ i ∈ Finset.range 192, stT149 (i+1)) + stT149 193 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 192
    simpa using h
  have hprev := st149_p192
  have hstep := st149_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p194 : ((1087632961127/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT149 (i+1))
      = (∑ i ∈ Finset.range 193, stT149 (i+1)) + stT149 194 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 193
    simpa using h
  have hprev := st149_p193
  have hstep := st149_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p195 : ((11191778902441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT149 (i+1))
      = (∑ i ∈ Finset.range 194, stT149 (i+1)) + stT149 195 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 194
    simpa using h
  have hprev := st149_p194
  have hstep := st149_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p196 : ((23072036402117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT149 (i+1))
      = (∑ i ∈ Finset.range 195, stT149 (i+1)) + stT149 196 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 195
    simpa using h
  have hprev := st149_p195
  have hstep := st149_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p197 : ((23440190312747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT149 (i+1))
      = (∑ i ∈ Finset.range 196, stT149 (i+1)) + stT149 197 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 196
    simpa using h
  have hprev := st149_p196
  have hstep := st149_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p198 : ((23291071847987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT149 (i+1))
      = (∑ i ∈ Finset.range 197, stT149 (i+1)) + stT149 198 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 197
    simpa using h
  have hprev := st149_p197
  have hstep := st149_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p199 : ((4541904413671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT149 (i+1))
      = (∑ i ∈ Finset.range 198, stT149 (i+1)) + stT149 199 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 198
    simpa using h
  have hprev := st149_p198
  have hstep := st149_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p200 : ((2751138302737/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT149 (i+1))
      = (∑ i ∈ Finset.range 199, stT149 (i+1)) + stT149 200 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 199
    simpa using h
  have hprev := st149_p199
  have hstep := st149_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p201 : ((10780155492527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT149 (i+1))
      = (∑ i ∈ Finset.range 200, stT149 (i+1)) + stT149 201 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 200
    simpa using h
  have hprev := st149_p200
  have hstep := st149_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p202 : ((5398832955533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT149 (i+1))
      = (∑ i ∈ Finset.range 201, stT149 (i+1)) + stT149 202 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 201
    simpa using h
  have hprev := st149_p201
  have hstep := st149_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p203 : ((5522928473891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT149 (i+1))
      = (∑ i ∈ Finset.range 202, stT149 (i+1)) + stT149 203 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 202
    simpa using h
  have hprev := st149_p202
  have hstep := st149_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p204 : ((5697709323071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT149 (i+1))
      = (∑ i ∈ Finset.range 203, stT149 (i+1)) + stT149 204 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 203
    simpa using h
  have hprev := st149_p203
  have hstep := st149_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p205 : ((2916973412473/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT149 (i+1))
      = (∑ i ∈ Finset.range 204, stT149 (i+1)) + stT149 205 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 204
    simpa using h
  have hprev := st149_p204
  have hstep := st149_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p206 : ((23453683580913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT149 (i+1))
      = (∑ i ∈ Finset.range 205, stT149 (i+1)) + stT149 206 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 205
    simpa using h
  have hprev := st149_p205
  have hstep := st149_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p207 : ((23089487635599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT149 (i+1))
      = (∑ i ∈ Finset.range 206, stT149 (i+1)) + stT149 207 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 206
    simpa using h
  have hprev := st149_p206
  have hstep := st149_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p208 : ((22427303154959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT149 (i+1))
      = (∑ i ∈ Finset.range 207, stT149 (i+1)) + stT149 208 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 207
    simpa using h
  have hprev := st149_p207
  have hstep := st149_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p209 : ((10896908707687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT149 (i+1))
      = (∑ i ∈ Finset.range 208, stT149 (i+1)) + stT149 209 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 208
    simpa using h
  have hprev := st149_p208
  have hstep := st149_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p210 : ((2686999237579/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT149 (i+1))
      = (∑ i ∈ Finset.range 209, stT149 (i+1)) + stT149 210 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 209
    simpa using h
  have hprev := st149_p209
  have hstep := st149_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p211 : ((1354627110821/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT149 (i+1))
      = (∑ i ∈ Finset.range 210, stT149 (i+1)) + stT149 211 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 210
    simpa using h
  have hprev := st149_p210
  have hstep := st149_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p212 : ((1111951297201/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT149 (i+1))
      = (∑ i ∈ Finset.range 211, stT149 (i+1)) + stT149 212 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 211
    simpa using h
  have hprev := st149_p211
  have hstep := st149_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p213 : ((5730247704917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT149 (i+1))
      = (∑ i ∈ Finset.range 212, stT149 (i+1)) + stT149 213 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 212
    simpa using h
  have hprev := st149_p212
  have hstep := st149_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p214 : ((23399946700673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT149 (i+1))
      = (∑ i ∈ Finset.range 213, stT149 (i+1)) + stT149 214 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 213
    simpa using h
  have hprev := st149_p213
  have hstep := st149_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p215 : ((4691119891411/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT149 (i+1))
      = (∑ i ∈ Finset.range 214, stT149 (i+1)) + stT149 215 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 214
    simpa using h
  have hprev := st149_p214
  have hstep := st149_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p216 : ((23065959019127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT149 (i+1))
      = (∑ i ∈ Finset.range 215, stT149 (i+1)) + stT149 216 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 215
    simpa using h
  have hprev := st149_p215
  have hstep := st149_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p217 : ((22412202772637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT149 (i+1))
      = (∑ i ∈ Finset.range 216, stT149 (i+1)) + stT149 217 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 216
    simpa using h
  have hprev := st149_p216
  have hstep := st149_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p218 : ((21791598160691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT149 (i+1))
      = (∑ i ∈ Finset.range 217, stT149 (i+1)) + stT149 218 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 217
    simpa using h
  have hprev := st149_p217
  have hstep := st149_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p219 : ((21481493207897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT149 (i+1))
      = (∑ i ∈ Finset.range 218, stT149 (i+1)) + stT149 219 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 218
    simpa using h
  have hprev := st149_p218
  have hstep := st149_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p220 : ((21616788766421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT149 (i+1))
      = (∑ i ∈ Finset.range 219, stT149 (i+1)) + stT149 220 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 219
    simpa using h
  have hprev := st149_p219
  have hstep := st149_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p221 : ((22134284080757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT149 (i+1))
      = (∑ i ∈ Finset.range 220, stT149 (i+1)) + stT149 221 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 220
    simpa using h
  have hprev := st149_p220
  have hstep := st149_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p222 : ((22805268264821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT149 (i+1))
      = (∑ i ∈ Finset.range 221, stT149 (i+1)) + stT149 222 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 221
    simpa using h
  have hprev := st149_p221
  have hstep := st149_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p223 : ((23338579407017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT149 (i+1))
      = (∑ i ∈ Finset.range 222, stT149 (i+1)) + stT149 223 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 222
    simpa using h
  have hprev := st149_p222
  have hstep := st149_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p224 : ((2350691454199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT149 (i+1))
      = (∑ i ∈ Finset.range 223, stT149 (i+1)) + stT149 224 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 223
    simpa using h
  have hprev := st149_p223
  have hstep := st149_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p225 : ((23241772409419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT149 (i+1))
      = (∑ i ∈ Finset.range 224, stT149 (i+1)) + stT149 225 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 224
    simpa using h
  have hprev := st149_p224
  have hstep := st149_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p226 : ((4531664814129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT149 (i+1))
      = (∑ i ∈ Finset.range 225, stT149 (i+1)) + stT149 226 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 225
    simpa using h
  have hprev := st149_p225
  have hstep := st149_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p227 : ((22002705468133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT149 (i+1))
      = (∑ i ∈ Finset.range 226, stT149 (i+1)) + stT149 227 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 226
    simpa using h
  have hprev := st149_p226
  have hstep := st149_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p228 : ((2693357475887/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT149 (i+1))
      = (∑ i ∈ Finset.range 227, stT149 (i+1)) + stT149 228 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 227
    simpa using h
  have hprev := st149_p227
  have hstep := st149_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p229 : ((5369062493827/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT149 (i+1))
      = (∑ i ∈ Finset.range 228, stT149 (i+1)) + stT149 229 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 228
    simpa using h
  have hprev := st149_p228
  have hstep := st149_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p230 : ((2727061174491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT149 (i+1))
      = (∑ i ∈ Finset.range 229, stT149 (i+1)) + stT149 230 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 229
    simpa using h
  have hprev := st149_p229
  have hstep := st149_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p231 : ((11213474088423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT149 (i+1))
      = (∑ i ∈ Finset.range 230, stT149 (i+1)) + stT149 231 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 230
    simpa using h
  have hprev := st149_p230
  have hstep := st149_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p232 : ((11530565585517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT149 (i+1))
      = (∑ i ∈ Finset.range 231, stT149 (i+1)) + stT149 232 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 231
    simpa using h
  have hprev := st149_p231
  have hstep := st149_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p233 : ((11733562688819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT149 (i+1))
      = (∑ i ∈ Finset.range 232, stT149 (i+1)) + stT149 233 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 232
    simpa using h
  have hprev := st149_p232
  have hstep := st149_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p234 : ((11743459355899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT149 (i+1))
      = (∑ i ∈ Finset.range 233, stT149 (i+1)) + stT149 234 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 233
    simpa using h
  have hprev := st149_p233
  have hstep := st149_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p235 : ((11557916113771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT149 (i+1))
      = (∑ i ∈ Finset.range 234, stT149 (i+1)) + stT149 235 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 234
    simpa using h
  have hprev := st149_p234
  have hstep := st149_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p236 : ((22500620853317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT149 (i+1))
      = (∑ i ∈ Finset.range 235, stT149 (i+1)) + stT149 236 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 235
    simpa using h
  have hprev := st149_p235
  have hstep := st149_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p237 : ((21879453951137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT149 (i+1))
      = (∑ i ∈ Finset.range 236, stT149 (i+1)) + stT149 237 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 236
    simpa using h
  have hprev := st149_p236
  have hstep := st149_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p238 : ((21488971972313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT149 (i+1))
      = (∑ i ∈ Finset.range 237, stT149 (i+1)) + stT149 238 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 237
    simpa using h
  have hprev := st149_p237
  have hstep := st149_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p239 : ((21474899168981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT149 (i+1))
      = (∑ i ∈ Finset.range 238, stT149 (i+1)) + stT149 239 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 238
    simpa using h
  have hprev := st149_p238
  have hstep := st149_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p240 : ((10919784735823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT149 (i+1))
      = (∑ i ∈ Finset.range 239, stT149 (i+1)) + stT149 240 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 239
    simpa using h
  have hprev := st149_p239
  have hstep := st149_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p241 : ((2244445707773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT149 (i+1))
      = (∑ i ∈ Finset.range 240, stT149 (i+1)) + stT149 241 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 240
    simpa using h
  have hprev := st149_p240
  have hstep := st149_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p242 : ((2306461510349/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT149 (i+1))
      = (∑ i ∈ Finset.range 241, stT149 (i+1)) + stT149 242 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 241
    simpa using h
  have hprev := st149_p241
  have hstep := st149_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p243 : ((2347302736149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT149 (i+1))
      = (∑ i ∈ Finset.range 242, stT149 (i+1)) + stT149 243 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 242
    simpa using h
  have hprev := st149_p242
  have hstep := st149_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p244 : ((2352307054477/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT149 (i+1))
      = (∑ i ∈ Finset.range 243, stT149 (i+1)) + stT149 244 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 243
    simpa using h
  have hprev := st149_p243
  have hstep := st149_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p245 : ((5799864405613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT149 (i+1))
      = (∑ i ∈ Finset.range 244, stT149 (i+1)) + stT149 245 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 244
    simpa using h
  have hprev := st149_p244
  have hstep := st149_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p246 : ((353447296363/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT149 (i+1))
      = (∑ i ∈ Finset.range 245, stT149 (i+1)) + stT149 246 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 245
    simpa using h
  have hprev := st149_p245
  have hstep := st149_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p247 : ((10996833043811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT149 (i+1))
      = (∑ i ∈ Finset.range 246, stT149 (i+1)) + stT149 247 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 246
    simpa using h
  have hprev := st149_p246
  have hstep := st149_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p248 : ((4307881465451/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT149 (i+1))
      = (∑ i ∈ Finset.range 247, stT149 (i+1)) + stT149 248 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 247
    simpa using h
  have hprev := st149_p247
  have hstep := st149_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p249 : ((4283006998731/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT149 (i+1))
      = (∑ i ∈ Finset.range 248, stT149 (i+1)) + stT149 249 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 248
    simpa using h
  have hprev := st149_p248
  have hstep := st149_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_p250 : ((4332225911741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT149 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT149 (i+1))
      = (∑ i ∈ Finset.range 249, stT149 (i+1)) + stT149 250 := by
    have h := Finset.sum_range_succ (fun i => stT149 (i+1)) 249
    simpa using h
  have hprev := st149_p249
  have hstep := st149_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st149_s250 :
    |Real.sin (((149 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))
      - ((-92117/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -731923/2500000) (δ := 7561/1000000000) (ψ := 771483/1000000) 149 131
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 149`** (evaluated boundary). -/
theorem station_149_sign : hardyG ((((149:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 149 250 (by norm_num) (by norm_num)
    ((771483/1000000 : ℚ) : ℝ)
  have hchain := st149_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT149 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((149 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((771483/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st149_c250
  have hsinb := abs_le.mp st149_s250
  have hbdy_lo : ((693435172681/7104400000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((149 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((771483/1000000 : ℚ) : ℝ))) / 2
          - ((((149:ℕ)):ℝ))
            * Real.sin (((149 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((771483/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((149:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((149:ℝ) * Real.log (250:ℝ) - ((771483/1000000 : ℚ) : ℝ))) / 2
        - ((149:ℝ)) * Real.sin ((149:ℝ) * Real.log (250:ℝ) - ((771483/1000000 : ℚ) : ℝ))
        ≥ ((5482091/40000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((149:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((5482091/40000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((5482091/40000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((5482091/40000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((149:ℕ)):ℝ))+1) * (((((149:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((6399901321/12500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((4332225911741/2000000000000 : ℚ) : ℝ) + ((693435172681/7104400000000 : ℚ) : ℝ)
      - ((6399901321/12500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((771483/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((149:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((771483/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((149:ℕ)):ℝ)))).re
      - Real.sin ((771483/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((149:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((149:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((149:ℕ)):ℝ))
      = (((((149:ℕ)):ℝ)) * (Real.log ((((149:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((149:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_149
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
  have hθwin : |(((771483/1000000 : ℚ) : ℝ) + ((26:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((149:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((149:ℕ)):ℝ)))
    (φ := ((771483/1000000 : ℚ) : ℝ) + ((26:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((771483/1000000 : ℚ) : ℝ) + ((26:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((771483/1000000 : ℚ)) : ℝ) - Real.pi) + ((26:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((771483/1000000 : ℚ)) : ℝ) - Real.pi) 26).1,
    (cos_sin_shift ((((771483/1000000 : ℚ)) : ℝ) - Real.pi) 26).2]
  exact cos_sin_flip ((771483/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_149_sign
end AxiomAudit
