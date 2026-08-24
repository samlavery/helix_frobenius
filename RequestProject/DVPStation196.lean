import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 196` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT196 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((196 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((2793/1000000 : ℚ) : ℝ))

theorem st196_c1 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3491/5000000) (δ := 201/1000000000) (ψ := 2793/1000000) 196 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t1 : ((499973/500000 : ℚ) : ℝ) ≤ stT196 1 := by
  have hc : ((499973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499973/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((499973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c2 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-720991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5940071/10000000) (δ := 2461/250000000) (ψ := 2793/1000000) 196 22
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t2 : ((-1274632485447/2500000000000 : ℚ) : ℝ) ≤ stT196 2 := by
  have hc : ((-721041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1274632485447/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-721041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c3 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-125777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4242269/10000000) (δ := 4923/500000000) (ψ := 2793/1000000) 196 34
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t3 : ((-726462561981/10000000000000 : ℚ) : ℝ) ≤ stT196 3 := by
  have hc : ((-125827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-726462561981/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-125827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c4 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((36857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 958707/2500000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 43
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t4 : ((36807/2000000 : ℚ) : ℝ) ≤ stT196 4 := by
  have hc : ((36807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36807/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((36807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c5 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((279253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 64389/200000) (δ := 249/25000000) (ψ := 2793/1000000) 196 50
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t5 : ((249726701681/2000000000000 : ℚ) : ℝ) ≤ stT196 5 := by
  have hc : ((279203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249726701681/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((279203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c6 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((779883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338159/2000000) (δ := 2451/250000000) (ψ := 2793/1000000) 196 56
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t6 : ((1591827092753/5000000000000 : ℚ) : ℝ) ≤ stT196 6 := by
  have hc : ((779833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1591827092753/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((779833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c7 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-75767/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73387/156250) (δ := 9939/1000000000) (ψ := 2793/1000000) 196 61
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t7 : ((-114567843311/1000000000000 : ℚ) : ℝ) ≤ stT196 7 := by
  have hc : ((-151559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114567843311/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-151559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c8 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((166997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419647/2000000) (δ := 623/62500000) (ψ := 2793/1000000) 196 65
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t8 : ((1180758420477/5000000000000 : ℚ) : ℝ) ≤ stT196 8 := by
  have hc : ((333969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1180758420477/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((333969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c9 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-967657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3608209/5000000) (δ := 9997/1000000000) (ψ := 2793/1000000) 196 69
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t9 : ((-1612845322569/5000000000000 : ℚ) : ℝ) ≤ stT196 9 := by
  have hc : ((-967707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1612845322569/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-967707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c10 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((466501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2713663/10000000) (δ := 4959/500000000) (ψ := 2793/1000000) 196 72
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t10 : ((1475047268927/10000000000000 : ℚ) : ℝ) ≤ stT196 10 := by
  have hc : ((466451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1475047268927/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((466451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c11 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((311313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627111/2000000) (δ := 123/12500000) (ψ := 2793/1000000) 196 75
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t11 : ((938493117719/10000000000000 : ℚ) : ℝ) ≤ stT196 11 := by
  have hc : ((311263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((938493117719/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((311263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c12 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-497883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7623859/10000000) (δ := 9841/1000000000) (ψ := 2793/1000000) 196 78
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t12 : ((-11229194647/39062500000 : ℚ) : ℝ) ≤ stT196 12 := by
  have hc : ((-124477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11229194647/39062500000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-124477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c13 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((15584/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90569/5000000) (δ := 1247/125000000) (ψ := 2793/1000000) 196 80
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t13 : ((2766083661/10000000000 : ℚ) : ℝ) ≤ stT196 13 := by
  have hc : ((498663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2766083661/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((498663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c14 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-444357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5078131/10000000) (δ := 9813/1000000000) (ψ := 2793/1000000) 196 82
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t14 : ((-1187727925491/10000000000000 : ℚ) : ℝ) ≤ stT196 14 := by
  have hc : ((-444407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1187727925491/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-444407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c15 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-19763/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 298749/400000) (δ := 4999/500000000) (ψ := 2793/1000000) 196 84
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t15 : ((-12757607649/50000000000 : ℚ) : ℝ) ≤ stT196 15 := by
  have hc : ((-4941/5000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12757607649/50000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-4941/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c16 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-498743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 959583/1250000) (δ := 9819/1000000000) (ψ := 2793/1000000) 196 86
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t16 : ((-77932531173/312500000000 : ℚ) : ℝ) ≤ stT196 16 := by
  have hc : ((-31173/31250 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77932531173/312500000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-31173/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c17 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-182089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5966791/10000000) (δ := 997/100000000) (ψ := 2793/1000000) 196 88
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t17 : ((-883322295471/5000000000000 : ℚ) : ℝ) ≤ stT196 17 := by
  have hc : ((-364203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-883322295471/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-364203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c18 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((65059/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2558481/10000000) (δ := 1231/125000000) (ψ := 2793/1000000) 196 90
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t18 : ((306661525821/2500000000000 : ℚ) : ℝ) ≤ stT196 18 := by
  have hc : ((260211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306661525821/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((260211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c19 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((9142/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1182259/5000000) (δ := 9941/1000000000) (ψ := 2793/1000000) 196 92
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t19 : ((671084511483/5000000000000 : ℚ) : ℝ) ≤ stT196 19 := by
  have hc : ((292519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671084511483/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((292519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c20 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-14846/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1765309/2500000) (δ := 4917/500000000) (ψ := 2793/1000000) 196 93
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t20 : ((-265587299649/1250000000000 : ℚ) : ℝ) ≤ stT196 20 := by
  have hc : ((-475097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265587299649/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-475097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c21 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((984023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111873/2500000) (δ := 39/3906250) (ψ := 2793/1000000) 196 95
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t21 : ((1073602116597/5000000000000 : ℚ) : ℝ) ≤ stT196 21 := by
  have hc : ((983973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1073602116597/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((983973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c22 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-221069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414959/625000) (δ := 1239/125000000) (ψ := 2793/1000000) 196 96
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t22 : ((-117836881663/625000000000 : ℚ) : ℝ) ≤ stT196 22 := by
  have hc : ((-442163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117836881663/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-442163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c23 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((364147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -936/3125) (δ := 1981/200000000) (ψ := 2793/1000000) 196 98
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t23 : ((94899334371/1250000000000 : ℚ) : ℝ) ≤ stT196 23 := by
  have hc : ((364097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94899334371/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((364097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c24 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((326061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3361/15625) (δ := 9991/1000000000) (ψ := 2793/1000000) 196 99
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t24 : ((166379512669/1250000000000 : ℚ) : ℝ) ≤ stT196 24 := by
  have hc : ((81509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166379512669/1250000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((81509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c25 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-211381/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6445857/10000000) (δ := 2471/250000000) (ψ := 2793/1000000) 196 100
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t25 : ((-845574422787/5000000000000 : ℚ) : ℝ) ≤ stT196 25 := by
  have hc : ((-422787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-845574422787/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-422787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c26 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-13337/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2875963/5000000) (δ := 4967/500000000) (ψ := 2793/1000000) 196 102
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t26 : ((-6539494689/50000000000 : ℚ) : ℝ) ≤ stT196 26 := by
  have hc : ((-6669/10000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6539494689/50000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-6669/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c27 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((23411/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2967143/10000000) (δ := 4981/500000000) (ψ := 2793/1000000) 196 103
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t27 : ((720775287/10000000000 : ℚ) : ℝ) ≤ stT196 27 := by
  have hc : ((187263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((720775287/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((187263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c28 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((188419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -854933/10000000) (δ := 1971/200000000) (ψ := 2793/1000000) 196 104
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t28 : ((178029736599/1000000000000 : ℚ) : ℝ) ≤ stT196 28 := by
  have hc : ((188409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178029736599/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((188409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c29 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((121029/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 631841/10000000) (δ := 1971/200000000) (ψ := 2793/1000000) 196 105
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t29 : ((898934234723/5000000000000 : ℚ) : ℝ) ≤ stT196 29 := by
  have hc : ((484091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((898934234723/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((484091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c30 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((817209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1535613/10000000) (δ := 9963/1000000000) (ψ := 2793/1000000) 196 106
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t30 : ((1491920689819/10000000000000 : ℚ) : ℝ) ≤ stT196 30 := by
  have hc : ((817159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1491920689819/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((817159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c31 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((145259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18947/100000) (δ := 9933/1000000000) (ψ := 2793/1000000) 196 107
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t31 : ((260874902197/2000000000000 : ℚ) : ℝ) ≤ stT196 31 := by
  have hc : ((145249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260874902197/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((145249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c32 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((766489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4359/25000) (δ := 4913/500000000) (ψ := 2793/1000000) 196 108
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t32 : ((677442402637/5000000000000 : ℚ) : ℝ) ≤ stT196 32 := by
  have hc : ((766439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677442402637/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((766439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c33 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((564/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1113721/10000000) (δ := 2471/250000000) (ψ := 2793/1000000) 196 109
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t33 : ((3926973059/25000000000 : ℚ) : ℝ) ≤ stT196 33 := by
  have hc : ((18047/20000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3926973059/25000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((18047/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c34 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((999909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 527/156250) (δ := 9991/1000000000) (ψ := 2793/1000000) 196 110
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t34 : ((342948637423/2000000000000 : ℚ) : ℝ) ≤ stT196 34 := by
  have hc : ((999859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((342948637423/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((999859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c35 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((207993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470361/10000000) (δ := 1981/200000000) (ψ := 2793/1000000) 196 111
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t35 : ((175775551497/1250000000000 : ℚ) : ℝ) ≤ stT196 35 := by
  have hc : ((415961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175775551497/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((415961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c36 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((219169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3374583/10000000) (δ := 4903/500000000) (ψ := 2793/1000000) 196 112
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t36 : ((182599093627/5000000000000 : ℚ) : ℝ) ≤ stT196 36 := by
  have hc : ((219119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182599093627/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((219119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c37 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-159523/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1414259/2500000) (δ := 9913/1000000000) (ψ := 2793/1000000) 196 113
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t37 : ((-52454953329/500000000000 : ℚ) : ℝ) ≤ stT196 37 := by
  have hc : ((-319071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52454953329/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-319071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c38 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-984299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3705191/5000000) (δ := 9913/1000000000) (ψ := 2793/1000000) 196 113
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t38 : ((-319365142607/2000000000000 : ℚ) : ℝ) ≤ stT196 38 := by
  have hc : ((-984349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319365142607/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-984349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c39 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-200011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4430413/10000000) (δ := 9983/1000000000) (ψ := 2793/1000000) 196 114
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t39 : ((-160177039101/5000000000000 : ℚ) : ℝ) ≤ stT196 39 := by
  have hc : ((-200061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160177039101/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-200061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c40 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((449947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 282043/2500000) (δ := 2469/250000000) (ψ := 2793/1000000) 196 115
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t40 : ((177847192809/1250000000000 : ℚ) : ℝ) ≤ stT196 40 := by
  have hc : ((224961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177847192809/1250000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((224961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c41 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((546877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2480417/10000000) (δ := 4917/500000000) (ψ := 2793/1000000) 196 116
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t41 : ((853999958499/10000000000000 : ℚ) : ℝ) ≤ stT196 41 := by
  have hc : ((546827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((853999958499/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((546827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c42 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-831291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1595139/2500000) (δ := 4971/500000000) (ψ := 2793/1000000) 196 117
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t42 : ((-641393714297/5000000000000 : ℚ) : ℝ) ≤ stT196 42 := by
  have hc : ((-831341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641393714297/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-831341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c43 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-469707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5149389/10000000) (δ := 4971/500000000) (ψ := 2793/1000000) 196 117
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t43 : ((-358186424201/5000000000000 : ℚ) : ℝ) ≤ stT196 43 := by
  have hc : ((-469757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358186424201/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-469757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c44 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((480179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17657/250000) (δ := 4977/500000000) (ψ := 2793/1000000) 196 118
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t44 : ((90482380453/625000000000 : ℚ) : ℝ) ≤ stT196 44 := by
  have hc : ((240077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90482380453/625000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((240077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c45 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-5041/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3990011/10000000) (δ := 9847/1000000000) (ψ := 2793/1000000) 196 119
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t45 : ((-941198289/250000000000 : ℚ) : ℝ) ≤ stT196 45 := by
  have hc : ((-5051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-941198289/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-5051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c46 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-909077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135593/200000) (δ := 9847/1000000000) (ψ := 2793/1000000) 196 119
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t46 : ((-67021751567/500000000000 : ℚ) : ℝ) ≤ stT196 46 := by
  have hc : ((-909127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67021751567/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-909127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c47 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((159951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 804887/5000000) (δ := 9863/1000000000) (ψ := 2793/1000000) 196 120
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t47 : ((233297779709/2000000000000 : ℚ) : ℝ) ≤ stT196 47 := by
  have hc : ((159941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233297779709/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((159941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c48 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((11591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3782023/10000000) (δ := 997/100000000) (ψ := 2793/1000000) 196 121
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t48 : ((133725807/16000000000 : ℚ) : ℝ) ≤ stT196 48 := by
  have hc : ((11581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133725807/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((11581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c49 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-817903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264277/2000000) (δ := 997/100000000) (ψ := 2793/1000000) 196 121
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t49 : ((-292126188279/2500000000000 : ℚ) : ℝ) ≤ stT196 49 := by
  have hc : ((-817953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292126188279/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-817953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c50 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((979037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 512793/10000000) (δ := 4963/500000000) (ψ := 2793/1000000) 196 122
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t50 : ((1384496142231/10000000000000 : ℚ) : ℝ) ≤ stT196 50 := by
  have hc : ((978987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1384496142231/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((978987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c51 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-585877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -686487/1250000) (δ := 4909/500000000) (ψ := 2793/1000000) 196 123
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t51 : ((-820462445487/10000000000000 : ℚ) : ℝ) ≤ stT196 51 := by
  have hc : ((-585927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-820462445487/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-585927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c52 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-38383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4022973/10000000) (δ := 4909/500000000) (ψ := 2793/1000000) 196 123
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t52 : ((-53297001183/10000000000000 : ℚ) : ℝ) ≤ stT196 52 := by
  have hc : ((-38433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53297001183/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-38433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c53 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((117869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -587843/2500000) (δ := 2473/250000000) (ψ := 2793/1000000) 196 124
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t53 : ((32378342339/400000000000 : ℚ) : ℝ) ≤ stT196 53 := by
  have hc : ((117859/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32378342339/400000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((117859/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c54 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-114213/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6807757/10000000) (δ := 2473/250000000) (ψ := 2793/1000000) 196 124
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t54 : ((-155432753539/1250000000000 : ℚ) : ℝ) ≤ stT196 54 := by
  have hc : ((-456877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155432753539/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-456877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c55 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((49967/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90853/10000000) (δ := 9999/1000000000) (ψ := 2793/1000000) 196 125
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t55 : ((134744163671/1000000000000 : ℚ) : ℝ) ≤ stT196 55 := by
  have hc : ((99929/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134744163671/1000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((99929/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c56 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-910471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3394023/5000000) (δ := 9897/1000000000) (ψ := 2793/1000000) 196 126
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t56 : ((-1216735585947/10000000000000 : ℚ) : ℝ) ≤ stT196 56 := by
  have hc : ((-910521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1216735585947/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-910521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c57 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((729023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 942379/5000000) (δ := 9897/1000000000) (ψ := 2793/1000000) 196 126
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t57 : ((241387016409/2500000000000 : ℚ) : ℝ) ≤ stT196 57 := by
  have hc : ((728973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241387016409/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((728973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c58 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-20897/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5301223/10000000) (δ := 9813/1000000000) (ψ := 2793/1000000) 196 127
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t58 : ((-5488349087/80000000000 : ℚ) : ℝ) ≤ stT196 58 := by
  have hc : ((-20899/40000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5488349087/80000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-20899/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c59 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((13369/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3075033/10000000) (δ := 9813/1000000000) (ψ := 2793/1000000) 196 127
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t59 : ((17402350263/400000000000 : ℚ) : ℝ) ≤ stT196 59 := by
  have hc : ((13367/40000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17402350263/400000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((13367/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c60 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-7483/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4397451/10000000) (δ := 31/3125000) (ψ := 2793/1000000) 196 128
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t60 : ((-386523903/16000000000 : ℚ) : ℝ) ≤ stT196 60 := by
  have hc : ((-1497/8000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386523903/16000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-1497/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c61 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((11239/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1850953/5000000) (δ := 31/3125000) (ψ := 2793/1000000) 196 128
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t61 : ((3595513413/312500000000 : ℚ) : ℝ) ≤ stT196 61 := by
  have hc : ((44931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3595513413/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((44931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c62 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-22277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4038413/10000000) (δ := 399/40000000) (ψ := 2793/1000000) 196 129
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t62 : ((-7080896151/1250000000000 : ℚ) : ℝ) ≤ stT196 62 := by
  have hc : ((-11151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7080896151/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-11151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c63 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((25031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3801783/10000000) (δ := 399/40000000) (ψ := 2793/1000000) 196 129
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t63 : ((15752292143/2500000000000 : ℚ) : ℝ) ≤ stT196 63 := by
  have hc : ((12503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15752292143/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((12503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c64 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-6551/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4189513/10000000) (δ := 2467/250000000) (ψ := 2793/1000000) 196 130
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t64 : ((-65541302433/5000000000000 : ℚ) : ℝ) ≤ stT196 64 := by
  have hc : ((-52433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65541302433/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-52433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c65 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((206287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 681509/2000000) (δ := 2467/250000000) (ψ := 2793/1000000) 196 130
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t65 : ((255805444239/10000000000000 : ℚ) : ℝ) ≤ stT196 65 := by
  have hc : ((206237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((255805444239/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((206237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c66 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-34941/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4819343/10000000) (δ := 4921/500000000) (ψ := 2793/1000000) 196 131
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t66 : ((-4301555559/100000000000 : ℚ) : ℝ) ≤ stT196 66 := by
  have hc : ((-17473/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4301555559/100000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-17473/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c67 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((523629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 637307/2500000) (δ := 4921/500000000) (ψ := 2793/1000000) 196 131
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t67 : ((319826661413/5000000000000 : ℚ) : ℝ) ≤ stT196 67 := by
  have hc : ((523579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319826661413/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((523579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c68 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-141921/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -737417/1250000) (δ := 9949/1000000000) (ψ := 2793/1000000) 196 132
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t68 : ((-172116743149/2000000000000 : ℚ) : ℝ) ≤ stT196 68 := by
  have hc : ((-141931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172116743149/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-141931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c69 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((548/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313519/2500000) (δ := 9949/1000000000) (ψ := 2793/1000000) 196 132
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t69 : ((2110965003/20000000000 : ℚ) : ℝ) ≤ stT196 69 := by
  have hc : ((3507/4000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2110965003/20000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((3507/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c70 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-245951/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296137/400000) (δ := 9947/1000000000) (ψ := 2793/1000000) 196 133
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t70 : ((-587965416283/5000000000000 : ℚ) : ℝ) ≤ stT196 70 := by
  have hc : ((-491927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587965416283/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-491927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c71 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((98363/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452971/10000000) (δ := 9947/1000000000) (ψ := 2793/1000000) 196 133
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t71 : ((58364702799/500000000000 : ℚ) : ℝ) ≤ stT196 71 := by
  have hc : ((49179/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58364702799/500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((49179/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c72 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-417829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1600079/2500000) (δ := 9947/1000000000) (ψ := 2793/1000000) 196 133
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t72 : ((-15388936039/156250000000 : ℚ) : ℝ) ≤ stT196 72 := by
  have hc : ((-208927/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15388936039/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-208927/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c73 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((523731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254893/1000000) (δ := 9839/1000000000) (ψ := 2793/1000000) 196 134
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t73 : ((612922002891/10000000000000 : ℚ) : ℝ) ≤ stT196 73 := by
  have hc : ((523681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((612922002891/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((523681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c74 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-15251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2058907/5000000) (δ := 9839/1000000000) (ψ := 2793/1000000) 196 134
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t74 : ((-17740561497/2000000000000 : ℚ) : ℝ) ≤ stT196 74 := by
  have hc : ((-15261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17740561497/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-15261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c75 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-52601/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501283/1000000) (δ := 9871/1000000000) (ψ := 2793/1000000) 196 135
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t75 : ((-242982576729/5000000000000 : ℚ) : ℝ) ≤ stT196 75 := by
  have hc : ((-210429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242982576729/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-210429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c76 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((103803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 738659/5000000) (δ := 9871/1000000000) (ψ := 2793/1000000) 196 135
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t76 : ((238125936793/2500000000000 : ℚ) : ℝ) ≤ stT196 76 := by
  have hc : ((415187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238125936793/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((415187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c77 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-499967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1956329/2500000) (δ := 4989/500000000) (ψ := 2793/1000000) 196 136
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t77 : ((-35612117697/312500000000 : ℚ) : ℝ) ≤ stT196 77 := by
  have hc : ((-62499/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35612117697/312500000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-62499/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c78 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((824737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30053/200000) (δ := 4989/500000000) (ψ := 2793/1000000) 196 136
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t78 : ((933774122299/10000000000000 : ℚ) : ℝ) ≤ stT196 78 := by
  have hc : ((824687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((933774122299/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((824687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c79 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-319297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 236973/500000) (δ := 4989/500000000) (ψ := 2793/1000000) 196 136
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t79 : ((-11227921173/312500000000 : ℚ) : ℝ) ≤ stT196 79 := by
  have hc : ((-319347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11227921173/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-319347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c80 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-85997/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1201223/2500000) (δ := 4959/500000000) (ψ := 2793/1000000) 196 137
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t80 : ((-96161545323/2500000000000 : ℚ) : ℝ) ≤ stT196 80 := by
  have hc : ((-172019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96161545323/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-172019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c81 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((217837/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1282133/10000000) (δ := 4959/500000000) (ψ := 2793/1000000) 196 137
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t81 : ((484054396039/5000000000000 : ℚ) : ℝ) ≤ stT196 81 := by
  have hc : ((435649/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((484054396039/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((435649/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c82 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-975061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3647241/5000000) (δ := 4959/500000000) (ψ := 2793/1000000) 196 137
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t82 : ((-269207669769/2500000000000 : ℚ) : ℝ) ≤ stT196 82 := by
  have hc : ((-975111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269207669769/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-975111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c83 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((274513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494799/2000000) (δ := 9811/1000000000) (ψ := 2793/1000000) 196 138
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t83 : ((18830597331/312500000000 : ℚ) : ℝ) ≤ stT196 83 := by
  have hc : ((34311/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18830597331/312500000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((34311/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c84 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((10573/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3394319/10000000) (δ := 1237/62500000) (ψ := 2793/1000000) 196 138
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t84 : ((23066712549/1000000000000 : ℚ) : ℝ) ≤ stT196 84 := by
  have hc : ((21141/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23066712549/1000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((21141/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c85 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-429959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1628691/2500000) (δ := 9899/1000000000) (ψ := 2793/1000000) 196 139
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t85 : ((-14574482361/156250000000 : ℚ) : ℝ) ≤ stT196 85 := by
  have hc : ((-13437/15625 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14574482361/156250000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-13437/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c86 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((951263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195931/2500000) (δ := 9899/1000000000) (ψ := 2793/1000000) 196 139
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t86 : ((1025718660651/10000000000000 : ℚ) : ℝ) ≤ stT196 86 := by
  have hc : ((951213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1025718660651/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((951213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c87 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-372453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4881117/10000000) (δ := 9899/1000000000) (ψ := 2793/1000000) 196 139
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t87 : ((-399365308839/10000000000000 : ℚ) : ℝ) ≤ stT196 87 := by
  have hc : ((-372503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-399365308839/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-372503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c88 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-62101/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -163337/312500) (δ := 2499/250000000) (ψ := 2793/1000000) 196 140
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t88 : ((-66206576929/1250000000000 : ℚ) : ℝ) ≤ stT196 88 := by
  have hc : ((-248429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66206576929/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-248429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c89 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((992323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309971/10000000) (δ := 2499/250000000) (ψ := 2793/1000000) 196 140
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t89 : ((1051806403181/10000000000000 : ℚ) : ℝ) ≤ stT196 89 := by
  have hc : ((992273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1051806403181/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((992273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c90 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-676617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 723111/1250000) (δ := 2499/250000000) (ψ := 2793/1000000) 196 140
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t90 : ((-713269948031/10000000000000 : ℚ) : ℝ) ≤ stT196 90 := by
  have hc : ((-676667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-713269948031/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-676667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c91 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-230569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -563581/1250000) (δ := 9857/500000000) (ψ := 2793/1000000) 196 141
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t91 : ((-48350887683/2000000000000 : ℚ) : ℝ) ≤ stT196 91 := by
  have hc : ((-230619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48350887683/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-230619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c92 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((943209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 423293/5000000) (δ := 9889/1000000000) (ψ := 2793/1000000) 196 141
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t92 : ((245827791237/2500000000000 : ℚ) : ℝ) ≤ stT196 92 := by
  have hc : ((943159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245827791237/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((943159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c93 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-387519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6143927/10000000) (δ := 9889/1000000000) (ψ := 2793/1000000) 196 141
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t93 : ((-6279133217/78125000000 : ℚ) : ℝ) ≤ stT196 93 := by
  have hc : ((-48443/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6279133217/78125000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-48443/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c94 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-39469/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4323339/10000000) (δ := 9821/1000000000) (ψ := 2793/1000000) 196 142
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t94 : ((-40722087693/2500000000000 : ℚ) : ℝ) ≤ stT196 94 := by
  have hc : ((-78963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40722087693/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-78963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c95 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((470579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 86189/1000000) (δ := 9821/1000000000) (ψ := 2793/1000000) 196 142
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t95 : ((120694512953/1250000000000 : ℚ) : ℝ) ≤ stT196 95 := by
  have hc : ((235277/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120694512953/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((235277/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c96 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-735453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5992827/10000000) (δ := 9821/1000000000) (ψ := 2793/1000000) 196 142
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t96 : ((-750669807363/10000000000000 : ℚ) : ℝ) ≤ stT196 96 := by
  have hc : ((-735503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750669807363/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-735503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c97 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-280341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1159341/2500000) (δ := 1241/125000000) (ψ := 2793/1000000) 196 143
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t97 : ((-284694160677/10000000000000 : ℚ) : ℝ) ≤ stT196 97 := by
  have hc : ((-280391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284694160677/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-280391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c98 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((987961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 388321/10000000) (δ := 1241/125000000) (ψ := 2793/1000000) 196 143
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t98 : ((124742534059/1250000000000 : ℚ) : ℝ) ≤ stT196 98 := by
  have hc : ((987911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124742534059/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((987911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c99 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-543333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5362997/10000000) (δ := 1241/125000000) (ψ := 2793/1000000) 196 143
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t99 : ((-273060281777/5000000000000 : ℚ) : ℝ) ≤ stT196 99 := by
  have hc : ((-543383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273060281777/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-543383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c100 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-281219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33877/62500) (δ := 623/62500000) (ψ := 2793/1000000) 196 144
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t100 : ((-70311/1250000 : ℚ) : ℝ) ≤ stT196 100 := by
  have hc : ((-70311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70311/1250000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-70311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c101 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((244091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34039/625000) (δ := 623/62500000) (ψ := 2793/1000000) 196 144
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t101 : ((485734276809/5000000000000 : ℚ) : ℝ) ≤ stT196 101 := by
  have hc : ((488157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((485734276809/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((488157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c102 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-35481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4283003/10000000) (δ := 623/62500000) (ψ := 2793/1000000) 196 144
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t102 : ((-17571909019/1250000000000 : ℚ) : ℝ) ≤ stT196 102 := by
  have hc : ((-70987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17571909019/1250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-70987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c103 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-55327/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6644471/10000000) (δ := 493/50000000) (ψ := 2793/1000000) 196 145
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t103 : ((-43614745653/500000000000 : ℚ) : ℝ) ≤ stT196 103 := by
  have hc : ((-442641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43614745653/500000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-442641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c104 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((180509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -95507/500000) (δ := 493/50000000) (ψ := 2793/1000000) 196 145
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t104 : ((17699125797/250000000000 : ℚ) : ℝ) ≤ stT196 104 := by
  have hc : ((360993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17699125797/250000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((360993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c105 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((221629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555783/2000000) (δ := 493/50000000) (ψ := 2793/1000000) 196 145
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t105 : ((540658359/12500000000 : ℚ) : ℝ) ≤ stT196 105 := by
  have hc : ((55401/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((540658359/12500000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((55401/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c106 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-98521/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3711739/5000000) (δ := 493/50000000) (ψ := 2793/1000000) 196 145
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t106 : ((-23924231109/250000000000 : ℚ) : ℝ) ≤ stT196 106 := by
  have hc : ((-49263/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23924231109/250000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-49263/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c107 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((97249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3683483/10000000) (δ := 197/20000000) (ψ := 2793/1000000) 196 146
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t107 : ((5872860779/625000000000 : ℚ) : ℝ) ≤ stT196 107 := by
  have hc : ((97199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5872860779/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((97199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c108 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((187883/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 874693/10000000) (δ := 197/20000000) (ψ := 2793/1000000) 196 146
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t108 : ((723123177/8000000000 : ℚ) : ℝ) ≤ stT196 108 := by
  have hc : ((187873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((723123177/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((187873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c109 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-110529/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5390827/10000000) (δ := 197/20000000) (ψ := 2793/1000000) 196 146
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t109 : ((-105877238753/2000000000000 : ℚ) : ℝ) ≤ stT196 109 := by
  have hc : ((-110539/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105877238753/2000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-110539/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c110 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-346661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5842211/10000000) (δ := 9957/1000000000) (ψ := 2793/1000000) 196 147
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t110 : ((-165276136809/2500000000000 : ℚ) : ℝ) ≤ stT196 110 := by
  have hc : ((-173343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165276136809/2500000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-173343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c111 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((422801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17597/125000) (δ := 9957/1000000000) (ψ := 2793/1000000) 196 147
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t111 : ((50160099979/625000000000 : ℚ) : ℝ) ≤ stT196 111 := by
  have hc : ((52847/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50160099979/625000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((52847/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c112 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((183627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1493427/5000000) (δ := 9957/1000000000) (ψ := 2793/1000000) 196 147
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t112 : ((86743774711/2500000000000 : ℚ) : ℝ) ≤ stT196 112 := by
  have hc : ((91801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86743774711/2500000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((91801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c113 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-979141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57363/78125) (δ := 9957/1000000000) (ψ := 2793/1000000) 196 147
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t113 : ((-921145536711/10000000000000 : ℚ) : ℝ) ≤ stT196 113 := by
  have hc : ((-979191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-921145536711/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-979191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c114 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-48507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2024153/5000000) (δ := 9939/1000000000) (ψ := 2793/1000000) 196 148
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t114 : ((-22738903201/5000000000000 : ℚ) : ℝ) ≤ stT196 114 := by
  have hc : ((-48557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22738903201/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-48557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c115 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((995727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 231207/10000000) (δ := 9939/1000000000) (ψ := 2793/1000000) 196 148
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t115 : ((116059098151/1250000000000 : ℚ) : ℝ) ≤ stT196 115 := by
  have hc : ((995677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116059098151/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((995677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c116 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-54229/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4473627/10000000) (δ := 9939/1000000000) (ψ := 2793/1000000) 196 148
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t116 : ((-100723970391/5000000000000 : ℚ) : ℝ) ≤ stT196 116 := by
  have hc : ((-108483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100723970391/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-108483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c117 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-945951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3514137/5000000) (δ := 1229/125000000) (ψ := 2793/1000000) 196 149
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t117 : ((-874578870501/10000000000000 : ℚ) : ℝ) ≤ stT196 117 := by
  have hc : ((-946001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-874578870501/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-946001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c118 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((414673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2858031/10000000) (δ := 1229/125000000) (ψ := 2793/1000000) 196 149
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t118 : ((190845576801/5000000000000 : ℚ) : ℝ) ≤ stT196 118 := by
  have hc : ((414623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190845576801/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((414623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c119 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((872357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1276981/10000000) (δ := 1229/125000000) (ψ := 2793/1000000) 196 149
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t119 : ((399821041143/5000000000000 : ℚ) : ℝ) ≤ stT196 119 := by
  have hc : ((872307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399821041143/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((872307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c120 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-548177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 672181/1250000) (δ := 1229/125000000) (ψ := 2793/1000000) 196 149
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t120 : ((-500460529717/10000000000000 : ℚ) : ℝ) ≤ stT196 120 := by
  have hc : ((-548227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500460529717/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-548227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c121 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-804507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6264103/10000000) (δ := 4939/500000000) (ψ := 2793/1000000) 196 150
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t121 : ((-731415527687/10000000000000 : ℚ) : ℝ) ≤ stT196 121 := by
  have hc : ((-804557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731415527687/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-804557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c122 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((78437/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1115579/5000000) (δ := 4939/500000000) (ψ := 2793/1000000) 196 150
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t122 : ((284031314111/5000000000000 : ℚ) : ℝ) ≤ stT196 122 := by
  have hc : ((313723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284031314111/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((313723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c123 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((759961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1768859/10000000) (δ := 4939/500000000) (ψ := 2793/1000000) 196 150
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t123 : ((685188191459/10000000000000 : ℚ) : ℝ) ≤ stT196 123 := by
  have hc : ((759911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((685188191459/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((759911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c124 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-165559/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5736487/10000000) (δ := 4939/500000000) (ψ := 2793/1000000) 196 150
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t124 : ((-297375354861/5000000000000 : ℚ) : ℝ) ≤ stT196 124 := by
  have hc : ((-331143/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297375354861/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-331143/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c125 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-746963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3017849/5000000) (δ := 4993/500000000) (ψ := 2793/1000000) 196 151
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t125 : ((-167037335891/2500000000000 : ℚ) : ℝ) ≤ stT196 125 := by
  have hc : ((-747013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167037335891/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-747013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c126 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((329047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -26641/125000) (δ := 4993/500000000) (ψ := 2793/1000000) 196 151
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t126 : ((14655791457/250000000000 : ℚ) : ℝ) ≤ stT196 126 := by
  have hc : ((164511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14655791457/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((164511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c127 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((191711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1742219/10000000) (δ := 4993/500000000) (ψ := 2793/1000000) 196 151
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t127 : ((85052407083/1250000000000 : ℚ) : ℝ) ≤ stT196 127 := by
  have hc : ((383397/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85052407083/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((383397/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c128 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-615767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5585387/10000000) (δ := 4993/500000000) (ψ := 2793/1000000) 196 151
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t128 : ((-136077698307/2500000000000 : ℚ) : ℝ) ≤ stT196 128 := by
  have hc : ((-615817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136077698307/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-615817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c129 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-101889/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6309299/10000000) (δ := 991/100000000) (ψ := 2793/1000000) 196 152
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t129 : ((-358855099031/5000000000000 : ℚ) : ℝ) ≤ stT196 129 := by
  have hc : ((-407581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-358855099031/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-407581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c130 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((106337/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2525519/10000000) (δ := 991/100000000) (ψ := 2793/1000000) 196 152
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t130 : ((46627472983/1000000000000 : ℚ) : ℝ) ≤ stT196 130 := by
  have hc : ((106327/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46627472983/1000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((106327/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c131 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((440761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 614651/5000000) (δ := 991/100000000) (ψ := 2793/1000000) 196 152
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t131 : ((1504190649/19531250000 : ℚ) : ℝ) ≤ stT196 131 := by
  have hc : ((13773/15625 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1504190649/19531250000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((13773/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c132 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-399917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1238889/2500000) (δ := 991/100000000) (ψ := 2793/1000000) 196 152
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t132 : ((-348126877163/10000000000000 : ℚ) : ℝ) ≤ stT196 132 := by
  have hc : ((-399967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-348126877163/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-399967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c133 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-949273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7054279/10000000) (δ := 9803/1000000000) (ψ := 2793/1000000) 196 153
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t133 : ((-82316746653/1000000000000 : ℚ) : ℝ) ≤ stT196 133 := by
  have hc : ((-949323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82316746653/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-949323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c134 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((215547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -169193/500000) (δ := 99/5000000) (ψ := 2793/1000000) 196 153
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t134 : ((46540240599/2500000000000 : ℚ) : ℝ) ≤ stT196 134 := by
  have hc : ((215497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46540240599/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((215497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c135 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((994627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51853/2000000) (δ := 9803/1000000000) (ψ := 2793/1000000) 196 153
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t135 : ((427997314987/5000000000000 : ℚ) : ℝ) ≤ stT196 135 := by
  have hc : ((994577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((427997314987/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((994577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c136 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((20589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1937757/5000000) (δ := 9803/1000000000) (ψ := 2793/1000000) 196 153
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t136 : ((4403007047/2500000000000 : ℚ) : ℝ) ≤ stT196 136 := by
  have hc : ((20539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4403007047/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((20539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c137 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-987939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7465303/10000000) (δ := 9803/1000000000) (ψ := 2793/1000000) 196 153
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t137 : ((-422048153031/5000000000000 : ℚ) : ℝ) ≤ stT196 137 := by
  have hc : ((-987989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-422048153031/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-987989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c138 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-148151/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4679037/10000000) (δ := 9907/1000000000) (ψ := 2793/1000000) 196 154
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t138 : ((-7883491077/312500000000 : ℚ) : ℝ) ≤ stT196 138 := by
  have hc : ((-9261/31250 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7883491077/312500000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-9261/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c139 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((897629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114109/1000000) (δ := 9907/1000000000) (ψ := 2793/1000000) 196 154
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t139 : ((190328934213/2500000000000 : ℚ) : ℝ) ≤ stT196 139 := by
  have hc : ((897579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190328934213/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((897579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c140 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((582829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 94859/400000) (δ := 9907/1000000000) (ψ := 2793/1000000) 196 154
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t140 : ((246269001483/5000000000000 : ℚ) : ℝ) ≤ stT196 140 := by
  have hc : ((582779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246269001483/5000000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((582779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c141 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-349073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5859001/10000000) (δ := 9907/1000000000) (ψ := 2793/1000000) 196 154
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t141 : ((-18374598681/312500000000 : ℚ) : ℝ) ≤ stT196 141 := by
  have hc : ((-174549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18374598681/312500000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-174549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c142 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-832507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1277207/2000000) (δ := 9989/1000000000) (ψ := 2793/1000000) 196 155
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t142 : ((-349333424187/5000000000000 : ℚ) : ℝ) ≤ stT196 142 := by
  have hc : ((-832557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349333424187/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-832557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c143 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((190941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2947411/10000000) (δ := 9989/1000000000) (ψ := 2793/1000000) 196 155
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t143 : ((19956497209/625000000000 : ℚ) : ℝ) ≤ stT196 143 := by
  have hc : ((47729/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19956497209/625000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((47729/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c144 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((245647/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467203/10000000) (δ := 9989/1000000000) (ψ := 2793/1000000) 196 155
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t144 : ((409390669577/5000000000000 : ℚ) : ℝ) ≤ stT196 144 := by
  have hc : ((491269/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409390669577/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((491269/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c145 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((13747/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 482281/1250000) (δ := 9989/1000000000) (ψ := 2793/1000000) 196 155
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t145 : ((2848872447/1250000000000 : ℚ) : ℝ) ≤ stT196 145 := by
  have hc : ((6861/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2848872447/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((6861/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c146 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-484307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7225969/10000000) (δ := 9989/1000000000) (ψ := 2793/1000000) 196 155
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t146 : ((-50104508649/625000000000 : ℚ) : ℝ) ≤ stT196 146 := by
  have hc : ((-121083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50104508649/625000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-121083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c147 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-232717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5137303/10000000) (δ := 9881/1000000000) (ψ := 2793/1000000) 196 156
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t147 : ((-95981287977/2500000000000 : ℚ) : ℝ) ≤ stT196 147 := by
  have hc : ((-116371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95981287977/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-116371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c148 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((74777/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7261/40000) (δ := 9881/1000000000) (ψ := 2793/1000000) 196 156
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t148 : ((7682766921/125000000000 : ℚ) : ℝ) ≤ stT196 148 := by
  have hc : ((18693/25000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7682766921/125000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((18693/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c149 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((82883/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1484459/10000000) (δ := 9881/1000000000) (ψ := 2793/1000000) 196 156
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t149 : ((33948113409/500000000000 : ℚ) : ℝ) ≤ stT196 149 := by
  have hc : ((41439/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33948113409/500000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((41439/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c150 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-81959/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 238101/500000) (δ := 9881/1000000000) (ψ := 2793/1000000) 196 156
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t150 : ((-133858967671/5000000000000 : ℚ) : ℝ) ≤ stT196 150 := by
  have hc : ((-163943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133858967671/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-163943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c151 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-249463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7690089/10000000) (δ := 9829/1000000000) (ψ := 2793/1000000) 196 157
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t151 : ((-406040835339/5000000000000 : ℚ) : ℝ) ≤ stT196 151 := by
  have hc : ((-498951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406040835339/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-498951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c152 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-209929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2227873/5000000) (δ := 9829/1000000000) (ψ := 2793/1000000) 196 157
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t152 : ((-42578911683/2500000000000 : ℚ) : ℝ) ≤ stT196 152 := by
  have hc : ((-209979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42578911683/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-209979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c153 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((439497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62131/500000) (δ := 9829/1000000000) (ψ := 2793/1000000) 196 157
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t153 : ((5551437771/78125000000 : ℚ) : ℝ) ≤ stT196 153 := by
  have hc : ((27467/31250 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5551437771/78125000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((27467/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c154 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((711031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1949583/10000000) (δ := 9829/1000000000) (ψ := 2793/1000000) 196 157
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t154 : ((286462065691/5000000000000 : ℚ) : ℝ) ≤ stT196 154 := by
  have hc : ((710981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286462065691/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((710981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c155 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-459691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1280277/2500000) (δ := 9829/1000000000) (ψ := 2793/1000000) 196 157
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t155 : ((-18463658301/500000000000 : ℚ) : ℝ) ≤ stT196 155 := by
  have hc : ((-459741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18463658301/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-459741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c156 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-986037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3717857/5000000) (δ := 621/62500000) (ψ := 2793/1000000) 196 158
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t156 : ((-789501681767/10000000000000 : ℚ) : ℝ) ≤ stT196 156 := by
  have hc : ((-986087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-789501681767/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-986087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c157 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-75257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538089/1250000) (δ := 621/62500000) (ψ := 2793/1000000) 196 158
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t157 : ((-30040792767/2500000000000 : ℚ) : ℝ) ≤ stT196 157 := by
  have hc : ((-37641/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30040792767/2500000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-37641/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c158 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((888173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298401/2500000) (δ := 621/62500000) (ψ := 2793/1000000) 196 158
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t158 : ((706552469511/10000000000000 : ℚ) : ℝ) ≤ stT196 158 := by
  have hc : ((888123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((706552469511/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((888123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c159 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((725413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 118619/625000) (δ := 621/62500000) (ψ := 2793/1000000) 196 158
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t159 : ((575249852513/10000000000000 : ℚ) : ℝ) ≤ stT196 159 := by
  have hc : ((725363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((575249852513/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((725363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c160 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-50651/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621251/1250000) (δ := 621/62500000) (ψ := 2793/1000000) 196 158
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t160 : ((-16019240853/500000000000 : ℚ) : ℝ) ≤ stT196 160 := by
  have hc : ((-202629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16019240853/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-202629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c161 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-997717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7685011/10000000) (δ := 249/25000000) (ψ := 2793/1000000) 196 159
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t161 : ((-786351148137/10000000000000 : ℚ) : ℝ) ≤ stT196 161 := by
  have hc : ((-997767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786351148137/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-997767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c162 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-142773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4650931/10000000) (δ := 249/25000000) (ψ := 2793/1000000) 196 159
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t162 : ((-2243856373/100000000000 : ℚ) : ℝ) ≤ stT196 162 := by
  have hc : ((-71399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2243856373/100000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-71399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c163 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((79353/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5111/31250) (δ := 249/25000000) (ψ := 2793/1000000) 196 159
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t163 : ((776876431/12500000000 : ℚ) : ℝ) ≤ stT196 163 := by
  have hc : ((19837/25000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((776876431/12500000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((19837/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c164 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((106919/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680709/5000000) (δ := 249/25000000) (ψ := 2793/1000000) 196 159
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t164 : ((83484745267/1250000000000 : ℚ) : ℝ) ≤ stT196 164 := by
  have hc : ((427651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83484745267/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((427651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c165 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-20563/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135629/312500) (δ := 249/25000000) (ψ := 2793/1000000) 196 159
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t165 : ((-64052562223/5000000000000 : ℚ) : ℝ) ≤ stT196 165 := by
  have hc : ((-82277/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64052562223/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-82277/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c166 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-121953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1460171/2000000) (δ := 249/25000000) (ψ := 2793/1000000) 196 159
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t166 : ((-378635175387/5000000000000 : ℚ) : ℝ) ≤ stT196 166 := by
  have hc : ((-487837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378635175387/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-487837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c167 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-576837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5464119/10000000) (δ := 9853/1000000000) (ψ := 2793/1000000) 196 160
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t167 : ((-6975140717/156250000000 : ℚ) : ℝ) ≤ stT196 167 := by
  have hc : ((-576887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6975140717/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-576887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c168 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((131797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253877/1000000) (δ := 9853/1000000000) (ψ := 2793/1000000) 196 160
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t168 : ((50836925151/1250000000000 : ℚ) : ℝ) ≤ stT196 168 := by
  have hc : ((263569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50836925151/1250000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((263569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c169 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((98911/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184641/5000000) (δ := 9853/1000000000) (ψ := 2793/1000000) 196 160
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t169 : ((3804073119/50000000000 : ℚ) : ℝ) ≤ stT196 169 := by
  have hc : ((49453/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3804073119/50000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((49453/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c170 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((26359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652027/2000000) (δ := 9853/1000000000) (ψ := 2793/1000000) 196 160
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t170 : ((2526571157/125000000000 : ℚ) : ℝ) ≤ stT196 170 := by
  have hc : ((13177/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2526571157/125000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((13177/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c171 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-772531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3067017/5000000) (δ := 9853/1000000000) (ψ := 2793/1000000) 196 160
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t171 : ((-7385101779/125000000000 : ℚ) : ℝ) ≤ stT196 171 := by
  have hc : ((-772581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7385101779/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-772581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c172 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-179663/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1679197/2500000) (δ := 9857/1000000000) (ψ := 2793/1000000) 196 161
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t172 : ((-136999404789/2000000000000 : ℚ) : ℝ) ≤ stT196 172 := by
  have hc : ((-179673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136999404789/2000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-179673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c173 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((20311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3876209/10000000) (δ := 9857/1000000000) (ψ := 2793/1000000) 196 161
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t173 : ((3080826877/2000000000000 : ℚ) : ℝ) ≤ stT196 173 := by
  have hc : ((20261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3080826877/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((20261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c174 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((912763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262999/2500000) (δ := 9857/1000000000) (ψ := 2793/1000000) 196 161
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t174 : ((345962949937/5000000000000 : ℚ) : ℝ) ≤ stT196 174 := by
  have hc : ((912713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345962949937/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((912713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c175 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((381641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1756047/10000000) (δ := 9857/1000000000) (ψ := 2793/1000000) 196 161
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t175 : ((2253704841/39062500000 : ℚ) : ℝ) ≤ stT196 175 := by
  have hc : ((23851/31250 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2253704841/39062500000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((23851/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c176 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-245883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4548067/10000000) (δ := 9857/1000000000) (ψ := 2793/1000000) 196 161
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t176 : ((-185379130807/10000000000000 : ℚ) : ℝ) ≤ stT196 176 := by
  have hc : ((-245933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185379130807/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-245933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c177 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-24441/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7324309/10000000) (δ := 9857/1000000000) (ψ := 2793/1000000) 196 161
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t177 : ((-73487775543/1000000000000 : ℚ) : ℝ) ≤ stT196 177 := by
  have hc : ((-97769/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73487775543/1000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-97769/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c178 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-31379/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1405773/2500000) (δ := 1993/200000000) (ψ := 2793/1000000) 196 162
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t178 : ((-11760719229/250000000000 : ℚ) : ℝ) ≤ stT196 178 := by
  have hc : ((-62763/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11760719229/250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-62763/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c179 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((81481/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -575593/2000000) (δ := 1993/200000000) (ψ := 2793/1000000) 196 162
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t179 : ((12178855377/400000000000 : ℚ) : ℝ) ≤ stT196 179 := by
  have hc : ((81471/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12178855377/400000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((81471/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c180 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((249561/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5927/400000) (δ := 1993/200000000) (ψ := 2793/1000000) 196 162
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t180 : ((74400888887/1000000000000 : ℚ) : ℝ) ≤ stT196 180 := by
  have hc : ((499097/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74400888887/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((499097/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c181 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((517723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2566523/10000000) (δ := 1993/200000000) (ψ := 2793/1000000) 196 162
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t181 : ((192391617431/5000000000000 : ℚ) : ℝ) ≤ stT196 181 := by
  have hc : ((517673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192391617431/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((517673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c182 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-255219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5266227/10000000) (δ := 1993/200000000) (ψ := 2793/1000000) 196 162
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t182 : ((-37839923/1000000000 : ℚ) : ℝ) ≤ stT196 182 := by
  have hc : ((-63811/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37839923/1000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-63811/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c183 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-249811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3878391/5000000) (δ := 9931/1000000000) (ψ := 2793/1000000) 196 163
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t183 : ((-184675027317/2500000000000 : ℚ) : ℝ) ≤ stT196 183 := by
  have hc : ((-499647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184675027317/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-499647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c184 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-89469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2543239/5000000) (δ := 9931/1000000000) (ψ := 2793/1000000) 196 163
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t184 : ((-6596481359/200000000000 : ℚ) : ℝ) ≤ stT196 184 := by
  have hc : ((-89479/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6596481359/200000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-89479/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c185 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((563441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2430629/10000000) (δ := 9931/1000000000) (ψ := 2793/1000000) 196 163
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t185 : ((207106475337/5000000000000 : ℚ) : ℝ) ≤ stT196 185 := by
  have hc : ((563391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207106475337/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((563391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c186 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((199289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 210863/10000000) (δ := 9931/1000000000) (ψ := 2793/1000000) 196 163
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t186 : ((29223667513/400000000000 : ℚ) : ℝ) ≤ stT196 186 := by
  have hc : ((199279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29223667513/400000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((199279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c187 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((421863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2838243/10000000) (δ := 9931/1000000000) (ψ := 2793/1000000) 196 163
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t187 : ((38557504517/1250000000000 : ℚ) : ℝ) ≤ stT196 187 := by
  have hc : ((421813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38557504517/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((421813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c188 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-286363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136289/250000) (δ := 9931/1000000000) (ψ := 2793/1000000) 196 163
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t188 : ((-2088699281/50000000000 : ℚ) : ℝ) ≤ stT196 188 := by
  have hc : ((-71597/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2088699281/50000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-71597/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c189 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-498447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -957113/1250000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t189 : ((-45323130437/625000000000 : ℚ) : ℝ) ≤ stT196 189 := by
  have hc : ((-62309/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45323130437/625000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-62309/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c190 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-220931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2535587/5000000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t190 : ((-40074624003/1250000000000 : ℚ) : ℝ) ≤ stT196 190 := by
  have hc : ((-55239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40074624003/1250000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-55239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c191 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((10813/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312371/1250000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t191 : ((977910261/25000000000 : ℚ) : ℝ) ≤ stT196 191 := by
  have hc : ((2703/5000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((977910261/25000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((2703/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c192 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((499857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59763/10000000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t192 : ((45090282073/625000000000 : ℚ) : ℝ) ≤ stT196 192 := by
  have hc : ((62479/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45090282073/625000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((62479/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c193 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((25221/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 521043/2000000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t193 : ((7261061831/200000000000 : ℚ) : ℝ) ≤ stT196 193 := by
  have hc : ((50437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7261061831/200000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((50437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c194 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-116379/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1027507/2000000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t194 : ((-167128649897/5000000000000 : ℚ) : ℝ) ≤ stT196 194 := by
  have hc : ((-232783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167128649897/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-232783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c195 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-249223/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7656821/10000000) (δ := 307/31250000) (ψ := 2793/1000000) 196 164
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t195 : ((-71392512033/1000000000000 : ℚ) : ℝ) ≤ stT196 195 := by
  have hc : ((-498471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71392512033/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-498471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c196 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-150719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5544743/10000000) (δ := 4943/500000000) (ψ := 2793/1000000) 196 165
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t196 : ((-107665400209/2500000000000 : ℚ) : ℝ) ≤ stT196 196 := by
  have hc : ((-301463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107665400209/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-301463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c197 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((343239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -762771/2500000) (δ := 4943/500000000) (ψ := 2793/1000000) 196 165
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t197 : ((24451186683/1000000000000 : ℚ) : ℝ) ≤ stT196 197 := by
  have hc : ((343189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24451186683/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((343189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c198 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((487057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570067/10000000) (δ := 4943/500000000) (ψ := 2793/1000000) 196 165
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t198 : ((43264818051/625000000000 : ℚ) : ℝ) ≤ stT196 198 := by
  have hc : ((60879/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43264818051/625000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((60879/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c199 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((362631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 379691/2000000) (δ := 4943/500000000) (ψ := 2793/1000000) 196 165
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t199 : ((128522251943/2500000000000 : ℚ) : ℝ) ≤ stT196 199 := by
  have hc : ((181303/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128522251943/2500000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((181303/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c200 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-170203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217729/500000) (δ := 4943/500000000) (ψ := 2793/1000000) 196 165
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t200 : ((-120387088071/10000000000000 : ℚ) : ℝ) ≤ stT196 200 := by
  have hc : ((-170253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120387088071/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-170253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c201 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-912193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 849813/1250000) (δ := 4943/500000000) (ψ := 2793/1000000) 196 165
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t201 : ((-321723475539/5000000000000 : ℚ) : ℝ) ≤ stT196 201 := by
  have hc : ((-912243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321723475539/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-912243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c202 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-106533/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -809717/1250000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 166
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t202 : ((-149921606443/2500000000000 : ℚ) : ℝ) ≤ stT196 202 := by
  have hc : ((-426157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149921606443/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-426157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c203 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-52367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4057969/10000000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 166
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t203 : ((-36789552871/10000000000000 : ℚ) : ℝ) ≤ stT196 203 := by
  have hc : ((-52417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36789552871/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-52417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c204 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((157993/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1650109/10000000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 166
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t204 : ((5530510881/100000000000 : ℚ) : ℝ) ≤ stT196 204 := by
  have hc : ((157983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5530510881/100000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((157983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c205 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((955809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 745991/10000000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 166
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t205 : ((66753075837/1000000000000 : ℚ) : ℝ) ≤ stT196 205 := by
  have hc : ((955759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66753075837/1000000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((955759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c206 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((313261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3130429/10000000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 166
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t206 : ((218224439663/10000000000000 : ℚ) : ℝ) ≤ stT196 206 := by
  have hc : ((313211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218224439663/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((313211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c207 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-589569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5503303/10000000) (δ := 9993/1000000000) (ψ := 2793/1000000) 196 166
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t207 : ((-409814096331/10000000000000 : ℚ) : ℝ) ≤ stT196 207 := by
  have hc : ((-589619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-409814096331/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-589619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c208 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-999991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1960801/2500000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t208 : ((-5417222097/78125000000 : ℚ) : ℝ) ≤ stT196 208 := by
  have hc : ((-1000041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5417222097/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-1000041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c209 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-36641/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2746533/5000000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t209 : ((-40555665479/1000000000000 : ℚ) : ℝ) ≤ stT196 209 := by
  have hc : ((-293153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40555665479/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-293153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c210 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((76059/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3154149/10000000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t210 : ((20990811209/1000000000000 : ℚ) : ℝ) ≤ stT196 210 := by
  have hc : ((152093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20990811209/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((152093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c211 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((945867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165271/2000000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t211 : ((162781726419/2500000000000 : ℚ) : ℝ) ≤ stT196 211 := by
  have hc : ((945817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162781726419/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((945817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c212 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((165499/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 745207/5000000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t212 : ((56829088089/1000000000000 : ℚ) : ℝ) ≤ stT196 212 := by
  have hc : ((165489/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56829088089/1000000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((165489/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c213 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((52251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 759261/2000000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t213 : ((8941874697/2500000000000 : ℚ) : ℝ) ≤ stT196 213 := by
  have hc : ((52201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8941874697/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((52201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c214 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-152319/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 761427/1250000) (δ := 9903/1000000000) (ψ := 2793/1000000) 196 167
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t214 : ((-52064985897/1000000000000 : ℚ) : ℝ) ≤ stT196 214 := by
  have hc : ((-152329/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52064985897/1000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-152329/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c215 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-122287/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7332167/10000000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t215 : ((-66722708027/1000000000000 : ℚ) : ℝ) ≤ stT196 215 := by
  have hc : ((-489173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66722708027/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-489173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c216 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-218631/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5058371/10000000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t216 : ((-2324634431/78125000000 : ℚ) : ℝ) ≤ stT196 216 := by
  have hc : ((-6833/15625 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2324634431/78125000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-6833/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c217 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((218721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279511/1000000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t217 : ((4639389607/156250000000 : ℚ) : ℝ) ≤ stT196 217 := by
  have hc : ((27337/62500 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4639389607/156250000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((27337/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c218 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((97657/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -542237/10000000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t218 : ((3306911741/50000000000 : ℚ) : ℝ) ≤ stT196 218 := by
  have hc : ((24413/25000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3306911741/50000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((24413/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c219 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((388743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 850173/5000000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t219 : ((131335567583/2500000000000 : ℚ) : ℝ) ≤ stT196 219 := by
  have hc : ((194359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131335567583/2500000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((194359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c220 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-2279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 245793/625000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t220 : ((-7851059/50000000000 : ℚ) : ℝ) ≤ stT196 220 := by
  have hc : ((-2329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7851059/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-2329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c221 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-777813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769367/1250000) (δ := 613/62500000) (ψ := 2793/1000000) 196 168
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t221 : ((-523247437799/10000000000000 : ℚ) : ℝ) ≤ stT196 221 := by
  have hc : ((-777863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-523247437799/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-777863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c222 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-979011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7340873/10000000) (δ := 1983/200000000) (ψ := 2793/1000000) 196 169
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t222 : ((-657103643577/10000000000000 : ℚ) : ℝ) ≤ stT196 222 := by
  have hc : ((-979061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657103643577/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-979061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c223 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-465899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5138617/10000000) (δ := 1983/200000000) (ψ := 2793/1000000) 196 169
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t223 : ((-6240454957/200000000000 : ℚ) : ℝ) ≤ stT196 223 := by
  have hc : ((-465949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6240454957/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-465949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c224 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((191163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -294621/1000000) (δ := 1983/200000000) (ψ := 2793/1000000) 196 169
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t224 : ((63854714057/2500000000000 : ℚ) : ℝ) ≤ stT196 224 := by
  have hc : ((95569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63854714057/2500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((95569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c225 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((23843/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381777/5000000) (δ := 1983/200000000) (ψ := 2793/1000000) 196 169
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t225 : ((31788968211/500000000000 : ℚ) : ℝ) ≤ stT196 225 := by
  have hc : ((95367/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31788968211/500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((95367/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c226 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((845257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451/3200) (δ := 2461/125000000) (ψ := 2793/1000000) 196 169
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t226 : ((56222324433/1000000000000 : ℚ) : ℝ) ≤ stT196 226 := by
  have hc : ((845207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56222324433/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((845207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c227 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((141223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14291/40000) (δ := 1983/200000000) (ψ := 2793/1000000) 196 169
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t227 : ((93699767079/10000000000000 : ℚ) : ℝ) ≤ stT196 227 := by
  have hc : ((141173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93699767079/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((141173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c228 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-131853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2863297/5000000) (δ := 1983/200000000) (ψ := 2793/1000000) 196 169
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t228 : ((-87328513421/2000000000000 : ℚ) : ℝ) ≤ stT196 228 := by
  have hc : ((-131863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87328513421/2000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-131863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c229 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-999977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3918467/5000000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t229 : ((-660836842113/10000000000000 : ℚ) : ℝ) ≤ stT196 229 := by
  have hc : ((-1000027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660836842113/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-1000027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c230 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-651793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5701857/10000000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t230 : ((-429812889183/10000000000000 : ℚ) : ℝ) ≤ stT196 230 := by
  have hc : ((-651843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-429812889183/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-651843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c231 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((139919/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3576041/10000000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t231 : ((92026948419/10000000000000 : ℚ) : ℝ) ≤ stT196 231 := by
  have hc : ((139869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92026948419/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((139869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c232 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((208597/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1459437/10000000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t232 : ((68471199477/1250000000000 : ℚ) : ℝ) ≤ stT196 232 := by
  have hc : ((417169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68471199477/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((417169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c233 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((193317/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324051/5000000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t233 : ((126639475147/2000000000000 : ℚ) : ℝ) ≤ stT196 233 := by
  have hc : ((193307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126639475147/2000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((193307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c234 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((454799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21973/80000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t234 : ((7431962907/250000000000 : ℚ) : ℝ) ≤ stT196 234 := by
  have hc : ((454749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7431962907/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((454749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c235 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-5558/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4836181/10000000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t235 : ((-116036934849/5000000000000 : ℚ) : ℝ) ≤ stT196 235 := by
  have hc : ((-177881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116036934849/5000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-177881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c236 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-232641/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1729217/2500000) (δ := 9981/1000000000) (ψ := 2793/1000000) 196 170
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t236 : ((-60577853023/1000000000000 : ℚ) : ℝ) ≤ stT196 236 := by
  have hc : ((-465307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60577853023/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-465307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c237 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-898743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1679807/2500000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t237 : ((-58382896901/1000000000000 : ℚ) : ℝ) ≤ stT196 237 := by
  have hc : ((-898793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58382896901/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-898793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c238 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-1797/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4656083/10000000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t238 : ((-4660100607/250000000000 : ℚ) : ℝ) ≤ stT196 238 := by
  have hc : ((-28757/100000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4660100607/250000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-28757/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c239 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((505681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1300781/5000000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t239 : ((163532694913/5000000000000 : ℚ) : ℝ) ≤ stT196 239 := by
  have hc : ((505631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163532694913/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((505631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c240 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((195081/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17363/312500) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t240 : ((125917745287/2000000000000 : ℚ) : ℝ) ≤ stT196 240 := by
  have hc : ((195071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125917745287/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((195071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c241 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((829423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 370451/2500000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t241 : ((133561398547/2500000000000 : ℚ) : ℝ) ≤ stT196 241 := by
  have hc : ((829373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133561398547/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((829373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c242 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((16571/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 877699/2500000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t242 : ((665563899/62500000000 : ℚ) : ℝ) ≤ stT196 242 := by
  have hc : ((8283/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((665563899/62500000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((8283/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c243 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-149653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5531409/10000000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t243 : ((-192021135831/5000000000000 : ℚ) : ℝ) ≤ stT196 243 := by
  have hc : ((-299331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-192021135831/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-299331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c244 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-99231/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7543741/10000000) (δ := 4937/500000000) (ψ := 2793/1000000) 196 171
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t244 : ((-3176469933/50000000000 : ℚ) : ℝ) ≤ stT196 244 := by
  have hc : ((-24809/25000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3176469933/50000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-24809/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c245 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-779121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6160147/10000000) (δ := 19767/1000000000) (ψ := 2793/1000000) 196 172
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t245 : ((-497794430967/10000000000000 : ℚ) : ℝ) ≤ stT196 245 := by
  have hc : ((-779171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497794430967/10000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-779171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c246 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((-94743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -832841/2000000) (δ := 2459/250000000) (ψ := 2793/1000000) 196 172
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t246 : ((-60437836561/10000000000000 : ℚ) : ℝ) ≤ stT196 246 := by
  have hc : ((-94793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60437836561/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-94793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c247 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((644407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2176373/10000000) (δ := 2459/250000000) (ψ := 2793/1000000) 196 172
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t247 : ((102498512347/2500000000000 : ℚ) : ℝ) ≤ stT196 247 := by
  have hc : ((644357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102498512347/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((644357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c248 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((99691/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196577/10000000) (δ := 2459/250000000) (ψ := 2793/1000000) 196 172
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t248 : ((6330061/100000000 : ℚ) : ℝ) ≤ stT196 248 := by
  have hc : ((49843/50000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6330061/100000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((49843/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c249 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((758301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13869/78125) (δ := 2459/250000000) (ψ := 2793/1000000) 196 172
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t249 : ((120130464181/2500000000000 : ℚ) : ℝ) ≤ stT196 249 := by
  have hc : ((758251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120130464181/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((758251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_c250 :
    |Real.cos (((196 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((15009/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3739201/10000000) (δ := 2459/250000000) (ψ := 2793/1000000) 196 172
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st196_t250 : ((1897238509/400000000000 : ℚ) : ℝ) ≤ stT196 250 := by
  have hc : ((14999/200000 : ℚ) : ℝ)
      ≤ Real.cos (((196 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st196_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1897238509/400000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((14999/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st196_p1 : ((499973/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT196 (i+1) := by
  rw [Finset.sum_range_one]
  exact st196_t1

theorem st196_p2 : ((1225232514553/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT196 (i+1))
      = (∑ i ∈ Finset.range 1, stT196 (i+1)) + stT196 2 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 1
    simpa using h
  have hprev := st196_p1
  have hstep := st196_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p3 : ((4174467496231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT196 (i+1))
      = (∑ i ∈ Finset.range 2, stT196 (i+1)) + stT196 3 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 2
    simpa using h
  have hprev := st196_p2
  have hstep := st196_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p4 : ((4358502496231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT196 (i+1))
      = (∑ i ∈ Finset.range 3, stT196 (i+1)) + stT196 4 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 3
    simpa using h
  have hprev := st196_p3
  have hstep := st196_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p5 : ((1401784001159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT196 (i+1))
      = (∑ i ∈ Finset.range 4, stT196 (i+1)) + stT196 5 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 4
    simpa using h
  have hprev := st196_p4
  have hstep := st196_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p6 : ((4395395095071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT196 (i+1))
      = (∑ i ∈ Finset.range 5, stT196 (i+1)) + stT196 6 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 5
    simpa using h
  have hprev := st196_p5
  have hstep := st196_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p7 : ((955638969629/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT196 (i+1))
      = (∑ i ∈ Finset.range 6, stT196 (i+1)) + stT196 7 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 6
    simpa using h
  have hprev := st196_p6
  have hstep := st196_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p8 : ((5003314298993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT196 (i+1))
      = (∑ i ∈ Finset.range 7, stT196 (i+1)) + stT196 8 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 7
    simpa using h
  have hprev := st196_p7
  have hstep := st196_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p9 : ((423808622053/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT196 (i+1))
      = (∑ i ∈ Finset.range 8, stT196 (i+1)) + stT196 9 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 8
    simpa using h
  have hprev := st196_p8
  have hstep := st196_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p10 : ((330239408871/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT196 (i+1))
      = (∑ i ∈ Finset.range 9, stT196 (i+1)) + stT196 10 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 9
    simpa using h
  have hprev := st196_p9
  have hstep := st196_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p11 : ((4597239169747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT196 (i+1))
      = (∑ i ∈ Finset.range 10, stT196 (i+1)) + stT196 11 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 10
    simpa using h
  have hprev := st196_p10
  have hstep := st196_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p12 : ((3159902254931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT196 (i+1))
      = (∑ i ∈ Finset.range 11, stT196 (i+1)) + stT196 12 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 11
    simpa using h
  have hprev := st196_p11
  have hstep := st196_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p13 : ((4542944085431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT196 (i+1))
      = (∑ i ∈ Finset.range 12, stT196 (i+1)) + stT196 13 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 12
    simpa using h
  have hprev := st196_p12
  have hstep := st196_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p14 : ((7898160245371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT196 (i+1))
      = (∑ i ∈ Finset.range 13, stT196 (i+1)) + stT196 14 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 13
    simpa using h
  have hprev := st196_p13
  have hstep := st196_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p15 : ((5346638715571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT196 (i+1))
      = (∑ i ∈ Finset.range 14, stT196 (i+1)) + stT196 15 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 14
    simpa using h
  have hprev := st196_p14
  have hstep := st196_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p16 : ((570559543607/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT196 (i+1))
      = (∑ i ∈ Finset.range 15, stT196 (i+1)) + stT196 16 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 15
    simpa using h
  have hprev := st196_p15
  have hstep := st196_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p17 : ((1086153127093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT196 (i+1))
      = (∑ i ∈ Finset.range 16, stT196 (i+1)) + stT196 17 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 16
    simpa using h
  have hprev := st196_p16
  have hstep := st196_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p18 : ((2312799230377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT196 (i+1))
      = (∑ i ∈ Finset.range 17, stT196 (i+1)) + stT196 18 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 17
    simpa using h
  have hprev := st196_p17
  have hstep := st196_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p19 : ((3654968253343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT196 (i+1))
      = (∑ i ∈ Finset.range 18, stT196 (i+1)) + stT196 19 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 18
    simpa using h
  have hprev := st196_p18
  have hstep := st196_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p20 : ((1530269856151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT196 (i+1))
      = (∑ i ∈ Finset.range 19, stT196 (i+1)) + stT196 20 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 19
    simpa using h
  have hprev := st196_p19
  have hstep := st196_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p21 : ((735494817869/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT196 (i+1))
      = (∑ i ∈ Finset.range 20, stT196 (i+1)) + stT196 21 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 20
    simpa using h
  have hprev := st196_p20
  have hstep := st196_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p22 : ((1792083982737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT196 (i+1))
      = (∑ i ∈ Finset.range 21, stT196 (i+1)) + stT196 22 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 21
    simpa using h
  have hprev := st196_p21
  have hstep := st196_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p23 : ((510255731541/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT196 (i+1))
      = (∑ i ∈ Finset.range 22, stT196 (i+1)) + stT196 23 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 22
    simpa using h
  have hprev := st196_p22
  have hstep := st196_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p24 : ((3882314759057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT196 (i+1))
      = (∑ i ∈ Finset.range 23, stT196 (i+1)) + stT196 24 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 23
    simpa using h
  have hprev := st196_p23
  have hstep := st196_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p25 : ((2191165913483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT196 (i+1))
      = (∑ i ∈ Finset.range 24, stT196 (i+1)) + stT196 25 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 24
    simpa using h
  have hprev := st196_p24
  have hstep := st196_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p26 : ((883266975683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT196 (i+1))
      = (∑ i ∈ Finset.range 25, stT196 (i+1)) + stT196 26 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 25
    simpa using h
  have hprev := st196_p25
  have hstep := st196_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p27 : ((1604042262683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT196 (i+1))
      = (∑ i ∈ Finset.range 26, stT196 (i+1)) + stT196 27 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 26
    simpa using h
  have hprev := st196_p26
  have hstep := st196_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p28 : ((3384339628673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT196 (i+1))
      = (∑ i ∈ Finset.range 27, stT196 (i+1)) + stT196 28 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 27
    simpa using h
  have hprev := st196_p27
  have hstep := st196_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p29 : ((5182208098119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT196 (i+1))
      = (∑ i ∈ Finset.range 28, stT196 (i+1)) + stT196 29 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 28
    simpa using h
  have hprev := st196_p28
  have hstep := st196_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p30 : ((3337064393969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT196 (i+1))
      = (∑ i ∈ Finset.range 29, stT196 (i+1)) + stT196 30 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 29
    simpa using h
  have hprev := st196_p29
  have hstep := st196_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p31 : ((7978503298923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT196 (i+1))
      = (∑ i ∈ Finset.range 30, stT196 (i+1)) + stT196 31 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 30
    simpa using h
  have hprev := st196_p30
  have hstep := st196_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p32 : ((9333388104197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT196 (i+1))
      = (∑ i ∈ Finset.range 31, stT196 (i+1)) + stT196 32 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 31
    simpa using h
  have hprev := st196_p31
  have hstep := st196_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p33 : ((10904177327797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT196 (i+1))
      = (∑ i ∈ Finset.range 32, stT196 (i+1)) + stT196 33 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 32
    simpa using h
  have hprev := st196_p32
  have hstep := st196_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p34 : ((394341266091/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT196 (i+1))
      = (∑ i ∈ Finset.range 33, stT196 (i+1)) + stT196 34 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 33
    simpa using h
  have hprev := st196_p33
  have hstep := st196_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p35 : ((1753140615861/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT196 (i+1))
      = (∑ i ∈ Finset.range 34, stT196 (i+1)) + stT196 35 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 34
    simpa using h
  have hprev := st196_p34
  have hstep := st196_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p36 : ((7195161557071/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT196 (i+1))
      = (∑ i ∈ Finset.range 35, stT196 (i+1)) + stT196 36 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 35
    simpa using h
  have hprev := st196_p35
  have hstep := st196_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p37 : ((6670612023781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT196 (i+1))
      = (∑ i ∈ Finset.range 36, stT196 (i+1)) + stT196 37 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 36
    simpa using h
  have hprev := st196_p36
  have hstep := st196_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p38 : ((11744398334527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT196 (i+1))
      = (∑ i ∈ Finset.range 37, stT196 (i+1)) + stT196 38 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 37
    simpa using h
  have hprev := st196_p37
  have hstep := st196_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p39 : ((456961770253/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT196 (i+1))
      = (∑ i ∈ Finset.range 38, stT196 (i+1)) + stT196 39 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 38
    simpa using h
  have hprev := st196_p38
  have hstep := st196_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p40 : ((12846821798797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT196 (i+1))
      = (∑ i ∈ Finset.range 39, stT196 (i+1)) + stT196 40 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 39
    simpa using h
  have hprev := st196_p39
  have hstep := st196_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p41 : ((856301359831/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT196 (i+1))
      = (∑ i ∈ Finset.range 40, stT196 (i+1)) + stT196 41 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 40
    simpa using h
  have hprev := st196_p40
  have hstep := st196_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p42 : ((6209017164351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT196 (i+1))
      = (∑ i ∈ Finset.range 41, stT196 (i+1)) + stT196 42 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 41
    simpa using h
  have hprev := st196_p41
  have hstep := st196_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p43 : ((117016614803/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT196 (i+1))
      = (∑ i ∈ Finset.range 42, stT196 (i+1)) + stT196 43 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 42
    simpa using h
  have hprev := st196_p42
  have hstep := st196_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p44 : ((3287344891887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT196 (i+1))
      = (∑ i ∈ Finset.range 43, stT196 (i+1)) + stT196 44 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 43
    simpa using h
  have hprev := st196_p43
  have hstep := st196_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p45 : ((3277932908997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT196 (i+1))
      = (∑ i ∈ Finset.range 44, stT196 (i+1)) + stT196 45 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 44
    simpa using h
  have hprev := st196_p44
  have hstep := st196_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p46 : ((1471412075581/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT196 (i+1))
      = (∑ i ∈ Finset.range 45, stT196 (i+1)) + stT196 46 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 45
    simpa using h
  have hprev := st196_p45
  have hstep := st196_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p47 : ((12937785503193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT196 (i+1))
      = (∑ i ∈ Finset.range 46, stT196 (i+1)) + stT196 47 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 46
    simpa using h
  have hprev := st196_p46
  have hstep := st196_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p48 : ((1627670516571/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT196 (i+1))
      = (∑ i ∈ Finset.range 47, stT196 (i+1)) + stT196 48 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 47
    simpa using h
  have hprev := st196_p47
  have hstep := st196_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p49 : ((2963214844863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT196 (i+1))
      = (∑ i ∈ Finset.range 48, stT196 (i+1)) + stT196 49 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 48
    simpa using h
  have hprev := st196_p48
  have hstep := st196_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p50 : ((13237355521683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT196 (i+1))
      = (∑ i ∈ Finset.range 49, stT196 (i+1)) + stT196 50 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 49
    simpa using h
  have hprev := st196_p49
  have hstep := st196_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p51 : ((3104223269049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT196 (i+1))
      = (∑ i ∈ Finset.range 50, stT196 (i+1)) + stT196 51 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 50
    simpa using h
  have hprev := st196_p50
  have hstep := st196_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p52 : ((12363596075013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT196 (i+1))
      = (∑ i ∈ Finset.range 51, stT196 (i+1)) + stT196 52 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 51
    simpa using h
  have hprev := st196_p51
  have hstep := st196_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p53 : ((823315914593/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT196 (i+1))
      = (∑ i ∈ Finset.range 52, stT196 (i+1)) + stT196 53 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 52
    simpa using h
  have hprev := st196_p52
  have hstep := st196_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p54 : ((1491199075647/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT196 (i+1))
      = (∑ i ∈ Finset.range 53, stT196 (i+1)) + stT196 54 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 53
    simpa using h
  have hprev := st196_p53
  have hstep := st196_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p55 : ((6638517120943/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT196 (i+1))
      = (∑ i ∈ Finset.range 54, stT196 (i+1)) + stT196 55 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 54
    simpa using h
  have hprev := st196_p54
  have hstep := st196_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p56 : ((12060298655939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT196 (i+1))
      = (∑ i ∈ Finset.range 55, stT196 (i+1)) + stT196 56 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 55
    simpa using h
  have hprev := st196_p55
  have hstep := st196_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p57 : ((521033868863/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT196 (i+1))
      = (∑ i ∈ Finset.range 56, stT196 (i+1)) + stT196 57 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 56
    simpa using h
  have hprev := st196_p56
  have hstep := st196_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p58 : ((123398030857/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT196 (i+1))
      = (∑ i ∈ Finset.range 57, stT196 (i+1)) + stT196 58 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 57
    simpa using h
  have hprev := st196_p57
  have hstep := st196_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p59 : ((510994473691/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT196 (i+1))
      = (∑ i ∈ Finset.range 58, stT196 (i+1)) + stT196 59 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 58
    simpa using h
  have hprev := st196_p58
  have hstep := st196_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p60 : ((125332844029/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT196 (i+1))
      = (∑ i ∈ Finset.range 59, stT196 (i+1)) + stT196 60 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 59
    simpa using h
  have hprev := st196_p59
  have hstep := st196_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p61 : ((3162085208029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT196 (i+1))
      = (∑ i ∈ Finset.range 60, stT196 (i+1)) + stT196 61 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 60
    simpa using h
  have hprev := st196_p60
  have hstep := st196_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p62 : ((3147923415727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT196 (i+1))
      = (∑ i ∈ Finset.range 61, stT196 (i+1)) + stT196 62 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 61
    simpa using h
  have hprev := st196_p61
  have hstep := st196_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p63 : ((316367570787/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT196 (i+1))
      = (∑ i ∈ Finset.range 62, stT196 (i+1)) + stT196 63 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 62
    simpa using h
  have hprev := st196_p62
  have hstep := st196_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p64 : ((6261810113307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT196 (i+1))
      = (∑ i ∈ Finset.range 63, stT196 (i+1)) + stT196 64 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 63
    simpa using h
  have hprev := st196_p63
  have hstep := st196_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p65 : ((12779425670853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT196 (i+1))
      = (∑ i ∈ Finset.range 64, stT196 (i+1)) + stT196 65 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 64
    simpa using h
  have hprev := st196_p64
  have hstep := st196_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p66 : ((12349270114953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT196 (i+1))
      = (∑ i ∈ Finset.range 65, stT196 (i+1)) + stT196 66 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 65
    simpa using h
  have hprev := st196_p65
  have hstep := st196_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p67 : ((12988923437779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT196 (i+1))
      = (∑ i ∈ Finset.range 66, stT196 (i+1)) + stT196 67 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 66
    simpa using h
  have hprev := st196_p66
  have hstep := st196_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p68 : ((6064169861017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT196 (i+1))
      = (∑ i ∈ Finset.range 67, stT196 (i+1)) + stT196 68 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 67
    simpa using h
  have hprev := st196_p67
  have hstep := st196_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p69 : ((6591911111767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT196 (i+1))
      = (∑ i ∈ Finset.range 68, stT196 (i+1)) + stT196 69 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 68
    simpa using h
  have hprev := st196_p68
  have hstep := st196_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p70 : ((1500986423871/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT196 (i+1))
      = (∑ i ∈ Finset.range 69, stT196 (i+1)) + stT196 70 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 69
    simpa using h
  have hprev := st196_p69
  have hstep := st196_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p71 : ((3293796361737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT196 (i+1))
      = (∑ i ∈ Finset.range 70, stT196 (i+1)) + stT196 71 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 70
    simpa using h
  have hprev := st196_p70
  have hstep := st196_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p72 : ((3047573385113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT196 (i+1))
      = (∑ i ∈ Finset.range 71, stT196 (i+1)) + stT196 72 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 71
    simpa using h
  have hprev := st196_p71
  have hstep := st196_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p73 : ((12803215543343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT196 (i+1))
      = (∑ i ∈ Finset.range 72, stT196 (i+1)) + stT196 73 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 72
    simpa using h
  have hprev := st196_p72
  have hstep := st196_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p74 : ((6357256367929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT196 (i+1))
      = (∑ i ∈ Finset.range 73, stT196 (i+1)) + stT196 74 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 73
    simpa using h
  have hprev := st196_p73
  have hstep := st196_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p75 : ((7642842239/6250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT196 (i+1))
      = (∑ i ∈ Finset.range 74, stT196 (i+1)) + stT196 75 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 74
    simpa using h
  have hprev := st196_p74
  have hstep := st196_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p76 : ((3295262832393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT196 (i+1))
      = (∑ i ∈ Finset.range 75, stT196 (i+1)) + stT196 76 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 75
    simpa using h
  have hprev := st196_p75
  have hstep := st196_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p77 : ((3010365890817/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT196 (i+1))
      = (∑ i ∈ Finset.range 76, stT196 (i+1)) + stT196 77 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 76
    simpa using h
  have hprev := st196_p76
  have hstep := st196_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p78 : ((12975237685567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT196 (i+1))
      = (∑ i ∈ Finset.range 77, stT196 (i+1)) + stT196 78 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 77
    simpa using h
  have hprev := st196_p77
  have hstep := st196_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p79 : ((12615944208031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT196 (i+1))
      = (∑ i ∈ Finset.range 78, stT196 (i+1)) + stT196 79 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 78
    simpa using h
  have hprev := st196_p78
  have hstep := st196_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p80 : ((12231298026739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT196 (i+1))
      = (∑ i ∈ Finset.range 79, stT196 (i+1)) + stT196 80 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 79
    simpa using h
  have hprev := st196_p79
  have hstep := st196_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p81 : ((13199406818817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT196 (i+1))
      = (∑ i ∈ Finset.range 80, stT196 (i+1)) + stT196 81 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 80
    simpa using h
  have hprev := st196_p80
  have hstep := st196_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p82 : ((12122576139741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT196 (i+1))
      = (∑ i ∈ Finset.range 81, stT196 (i+1)) + stT196 82 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 81
    simpa using h
  have hprev := st196_p81
  have hstep := st196_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p83 : ((12725155254333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT196 (i+1))
      = (∑ i ∈ Finset.range 82, stT196 (i+1)) + stT196 83 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 82
    simpa using h
  have hprev := st196_p82
  have hstep := st196_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p84 : ((12955822379823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT196 (i+1))
      = (∑ i ∈ Finset.range 83, stT196 (i+1)) + stT196 84 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 83
    simpa using h
  have hprev := st196_p83
  have hstep := st196_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p85 : ((12023055508719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT196 (i+1))
      = (∑ i ∈ Finset.range 84, stT196 (i+1)) + stT196 85 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 84
    simpa using h
  have hprev := st196_p84
  have hstep := st196_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p86 : ((1304877416937/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT196 (i+1))
      = (∑ i ∈ Finset.range 85, stT196 (i+1)) + stT196 86 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 85
    simpa using h
  have hprev := st196_p85
  have hstep := st196_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p87 : ((12649408860531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT196 (i+1))
      = (∑ i ∈ Finset.range 86, stT196 (i+1)) + stT196 87 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 86
    simpa using h
  have hprev := st196_p86
  have hstep := st196_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p88 : ((12119756245099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT196 (i+1))
      = (∑ i ∈ Finset.range 87, stT196 (i+1)) + stT196 88 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 87
    simpa using h
  have hprev := st196_p87
  have hstep := st196_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p89 : ((329289066207/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT196 (i+1))
      = (∑ i ∈ Finset.range 88, stT196 (i+1)) + stT196 89 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 88
    simpa using h
  have hprev := st196_p88
  have hstep := st196_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p90 : ((12458292700249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT196 (i+1))
      = (∑ i ∈ Finset.range 89, stT196 (i+1)) + stT196 90 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 89
    simpa using h
  have hprev := st196_p89
  have hstep := st196_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p91 : ((6108269130917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT196 (i+1))
      = (∑ i ∈ Finset.range 90, stT196 (i+1)) + stT196 91 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 90
    simpa using h
  have hprev := st196_p90
  have hstep := st196_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p92 : ((6599924713391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT196 (i+1))
      = (∑ i ∈ Finset.range 91, stT196 (i+1)) + stT196 92 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 91
    simpa using h
  have hprev := st196_p91
  have hstep := st196_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p93 : ((6198060187503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT196 (i+1))
      = (∑ i ∈ Finset.range 92, stT196 (i+1)) + stT196 93 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 92
    simpa using h
  have hprev := st196_p92
  have hstep := st196_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p94 : ((6116616012117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT196 (i+1))
      = (∑ i ∈ Finset.range 93, stT196 (i+1)) + stT196 94 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 93
    simpa using h
  have hprev := st196_p93
  have hstep := st196_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p95 : ((6599394063929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT196 (i+1))
      = (∑ i ∈ Finset.range 94, stT196 (i+1)) + stT196 95 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 94
    simpa using h
  have hprev := st196_p94
  have hstep := st196_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p96 : ((2489623664099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT196 (i+1))
      = (∑ i ∈ Finset.range 95, stT196 (i+1)) + stT196 96 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 95
    simpa using h
  have hprev := st196_p95
  have hstep := st196_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p97 : ((6081712079909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT196 (i+1))
      = (∑ i ∈ Finset.range 96, stT196 (i+1)) + stT196 97 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 96
    simpa using h
  have hprev := st196_p96
  have hstep := st196_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p98 : ((1316136443229/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT196 (i+1))
      = (∑ i ∈ Finset.range 97, stT196 (i+1)) + stT196 98 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 97
    simpa using h
  have hprev := st196_p97
  have hstep := st196_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p99 : ((197113185449/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT196 (i+1))
      = (∑ i ∈ Finset.range 98, stT196 (i+1)) + stT196 99 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 98
    simpa using h
  have hprev := st196_p98
  have hstep := st196_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p100 : ((188324310449/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT196 (i+1))
      = (∑ i ∈ Finset.range 99, stT196 (i+1)) + stT196 100 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 99
    simpa using h
  have hprev := st196_p99
  have hstep := st196_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p101 : ((6512112211177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT196 (i+1))
      = (∑ i ∈ Finset.range 100, stT196 (i+1)) + stT196 101 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 100
    simpa using h
  have hprev := st196_p100
  have hstep := st196_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p102 : ((6441824575101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT196 (i+1))
      = (∑ i ∈ Finset.range 101, stT196 (i+1)) + stT196 102 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 101
    simpa using h
  have hprev := st196_p101
  have hstep := st196_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p103 : ((6005677118571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT196 (i+1))
      = (∑ i ∈ Finset.range 102, stT196 (i+1)) + stT196 103 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 102
    simpa using h
  have hprev := st196_p102
  have hstep := st196_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p104 : ((6359659634511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT196 (i+1))
      = (∑ i ∈ Finset.range 103, stT196 (i+1)) + stT196 104 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 103
    simpa using h
  have hprev := st196_p103
  have hstep := st196_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p105 : ((6575922978111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT196 (i+1))
      = (∑ i ∈ Finset.range 104, stT196 (i+1)) + stT196 105 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 104
    simpa using h
  have hprev := st196_p104
  have hstep := st196_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p106 : ((6097438355931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT196 (i+1))
      = (∑ i ∈ Finset.range 105, stT196 (i+1)) + stT196 106 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 105
    simpa using h
  have hprev := st196_p105
  have hstep := st196_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p107 : ((6144421242163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT196 (i+1))
      = (∑ i ∈ Finset.range 106, stT196 (i+1)) + stT196 107 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 106
    simpa using h
  have hprev := st196_p106
  have hstep := st196_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p108 : ((1649093306947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT196 (i+1))
      = (∑ i ∈ Finset.range 107, stT196 (i+1)) + stT196 108 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 107
    simpa using h
  have hprev := st196_p107
  have hstep := st196_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p109 : ((12663360261811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT196 (i+1))
      = (∑ i ∈ Finset.range 108, stT196 (i+1)) + stT196 109 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 108
    simpa using h
  have hprev := st196_p108
  have hstep := st196_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p110 : ((480090228583/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT196 (i+1))
      = (∑ i ∈ Finset.range 109, stT196 (i+1)) + stT196 110 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 109
    simpa using h
  have hprev := st196_p109
  have hstep := st196_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p111 : ((12804817314239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT196 (i+1))
      = (∑ i ∈ Finset.range 110, stT196 (i+1)) + stT196 111 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 110
    simpa using h
  have hprev := st196_p110
  have hstep := st196_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p112 : ((13151792413083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT196 (i+1))
      = (∑ i ∈ Finset.range 111, stT196 (i+1)) + stT196 112 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 111
    simpa using h
  have hprev := st196_p111
  have hstep := st196_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p113 : ((3057661719093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT196 (i+1))
      = (∑ i ∈ Finset.range 112, stT196 (i+1)) + stT196 113 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 112
    simpa using h
  have hprev := st196_p112
  have hstep := st196_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p114 : ((1218516906997/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT196 (i+1))
      = (∑ i ∈ Finset.range 113, stT196 (i+1)) + stT196 114 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 113
    simpa using h
  have hprev := st196_p113
  have hstep := st196_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p115 : ((6556820927589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT196 (i+1))
      = (∑ i ∈ Finset.range 114, stT196 (i+1)) + stT196 115 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 114
    simpa using h
  have hprev := st196_p114
  have hstep := st196_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p116 : ((3228048478599/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT196 (i+1))
      = (∑ i ∈ Finset.range 115, stT196 (i+1)) + stT196 116 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 115
    simpa using h
  have hprev := st196_p115
  have hstep := st196_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p117 : ((2407523008779/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT196 (i+1))
      = (∑ i ∈ Finset.range 116, stT196 (i+1)) + stT196 117 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 116
    simpa using h
  have hprev := st196_p116
  have hstep := st196_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p118 : ((12419306197497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT196 (i+1))
      = (∑ i ∈ Finset.range 117, stT196 (i+1)) + stT196 118 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 117
    simpa using h
  have hprev := st196_p117
  have hstep := st196_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p119 : ((13218948279783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT196 (i+1))
      = (∑ i ∈ Finset.range 118, stT196 (i+1)) + stT196 119 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 118
    simpa using h
  have hprev := st196_p118
  have hstep := st196_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p120 : ((6359243875033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT196 (i+1))
      = (∑ i ∈ Finset.range 119, stT196 (i+1)) + stT196 120 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 119
    simpa using h
  have hprev := st196_p119
  have hstep := st196_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p121 : ((11987072222379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT196 (i+1))
      = (∑ i ∈ Finset.range 120, stT196 (i+1)) + stT196 121 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 120
    simpa using h
  have hprev := st196_p120
  have hstep := st196_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p122 : ((12555134850601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT196 (i+1))
      = (∑ i ∈ Finset.range 121, stT196 (i+1)) + stT196 122 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 121
    simpa using h
  have hprev := st196_p121
  have hstep := st196_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p123 : ((662016152103/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT196 (i+1))
      = (∑ i ∈ Finset.range 122, stT196 (i+1)) + stT196 123 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 122
    simpa using h
  have hprev := st196_p122
  have hstep := st196_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p124 : ((6322786166169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT196 (i+1))
      = (∑ i ∈ Finset.range 123, stT196 (i+1)) + stT196 124 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 123
    simpa using h
  have hprev := st196_p123
  have hstep := st196_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p125 : ((5988711494387/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT196 (i+1))
      = (∑ i ∈ Finset.range 124, stT196 (i+1)) + stT196 125 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 124
    simpa using h
  have hprev := st196_p124
  have hstep := st196_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p126 : ((6281827323527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT196 (i+1))
      = (∑ i ∈ Finset.range 125, stT196 (i+1)) + stT196 126 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 125
    simpa using h
  have hprev := st196_p125
  have hstep := st196_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p127 : ((6622036951859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT196 (i+1))
      = (∑ i ∈ Finset.range 126, stT196 (i+1)) + stT196 127 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 126
    simpa using h
  have hprev := st196_p126
  have hstep := st196_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p128 : ((1269976311049/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT196 (i+1))
      = (∑ i ∈ Finset.range 127, stT196 (i+1)) + stT196 128 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 127
    simpa using h
  have hprev := st196_p127
  have hstep := st196_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p129 : ((2995513228107/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT196 (i+1))
      = (∑ i ∈ Finset.range 128, stT196 (i+1)) + stT196 129 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 128
    simpa using h
  have hprev := st196_p128
  have hstep := st196_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p130 : ((6224163821129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT196 (i+1))
      = (∑ i ∈ Finset.range 129, stT196 (i+1)) + stT196 130 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 129
    simpa using h
  have hprev := st196_p129
  have hstep := st196_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p131 : ((6609236627273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT196 (i+1))
      = (∑ i ∈ Finset.range 130, stT196 (i+1)) + stT196 131 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 130
    simpa using h
  have hprev := st196_p130
  have hstep := st196_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p132 : ((12870346377383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT196 (i+1))
      = (∑ i ∈ Finset.range 131, stT196 (i+1)) + stT196 132 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 131
    simpa using h
  have hprev := st196_p131
  have hstep := st196_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p133 : ((12047178910853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT196 (i+1))
      = (∑ i ∈ Finset.range 132, stT196 (i+1)) + stT196 133 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 132
    simpa using h
  have hprev := st196_p132
  have hstep := st196_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p134 : ((12233339873249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT196 (i+1))
      = (∑ i ∈ Finset.range 133, stT196 (i+1)) + stT196 134 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 133
    simpa using h
  have hprev := st196_p133
  have hstep := st196_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p135 : ((13089334503223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT196 (i+1))
      = (∑ i ∈ Finset.range 134, stT196 (i+1)) + stT196 135 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 134
    simpa using h
  have hprev := st196_p134
  have hstep := st196_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p136 : ((13106946531411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT196 (i+1))
      = (∑ i ∈ Finset.range 135, stT196 (i+1)) + stT196 136 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 135
    simpa using h
  have hprev := st196_p135
  have hstep := st196_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p137 : ((12262850225349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT196 (i+1))
      = (∑ i ∈ Finset.range 136, stT196 (i+1)) + stT196 137 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 136
    simpa using h
  have hprev := st196_p136
  have hstep := st196_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p138 : ((2402115702177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT196 (i+1))
      = (∑ i ∈ Finset.range 137, stT196 (i+1)) + stT196 138 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 137
    simpa using h
  have hprev := st196_p137
  have hstep := st196_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p139 : ((12771894247737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT196 (i+1))
      = (∑ i ∈ Finset.range 138, stT196 (i+1)) + stT196 139 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 138
    simpa using h
  have hprev := st196_p138
  have hstep := st196_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p140 : ((13264432250703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT196 (i+1))
      = (∑ i ∈ Finset.range 139, stT196 (i+1)) + stT196 140 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 139
    simpa using h
  have hprev := st196_p139
  have hstep := st196_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p141 : ((12676445092911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT196 (i+1))
      = (∑ i ∈ Finset.range 140, stT196 (i+1)) + stT196 141 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 140
    simpa using h
  have hprev := st196_p140
  have hstep := st196_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p142 : ((11977778244537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT196 (i+1))
      = (∑ i ∈ Finset.range 141, stT196 (i+1)) + stT196 142 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 141
    simpa using h
  have hprev := st196_p141
  have hstep := st196_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p143 : ((12297082199881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT196 (i+1))
      = (∑ i ∈ Finset.range 142, stT196 (i+1)) + stT196 143 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 142
    simpa using h
  have hprev := st196_p142
  have hstep := st196_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p144 : ((2623172707807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT196 (i+1))
      = (∑ i ∈ Finset.range 143, stT196 (i+1)) + stT196 144 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 143
    simpa using h
  have hprev := st196_p143
  have hstep := st196_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p145 : ((13138654518611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT196 (i+1))
      = (∑ i ∈ Finset.range 144, stT196 (i+1)) + stT196 145 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 144
    simpa using h
  have hprev := st196_p144
  have hstep := st196_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p146 : ((12336982380227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT196 (i+1))
      = (∑ i ∈ Finset.range 145, stT196 (i+1)) + stT196 146 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 145
    simpa using h
  have hprev := st196_p145
  have hstep := st196_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p147 : ((11953057228319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT196 (i+1))
      = (∑ i ∈ Finset.range 146, stT196 (i+1)) + stT196 147 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 146
    simpa using h
  have hprev := st196_p146
  have hstep := st196_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p148 : ((12567678581999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT196 (i+1))
      = (∑ i ∈ Finset.range 147, stT196 (i+1)) + stT196 148 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 147
    simpa using h
  have hprev := st196_p147
  have hstep := st196_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p149 : ((13246640850179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT196 (i+1))
      = (∑ i ∈ Finset.range 148, stT196 (i+1)) + stT196 149 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 148
    simpa using h
  have hprev := st196_p148
  have hstep := st196_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p150 : ((12978922914837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT196 (i+1))
      = (∑ i ∈ Finset.range 149, stT196 (i+1)) + stT196 150 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 149
    simpa using h
  have hprev := st196_p149
  have hstep := st196_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p151 : ((12166841244159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT196 (i+1))
      = (∑ i ∈ Finset.range 150, stT196 (i+1)) + stT196 151 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 150
    simpa using h
  have hprev := st196_p150
  have hstep := st196_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p152 : ((11996525597427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT196 (i+1))
      = (∑ i ∈ Finset.range 151, stT196 (i+1)) + stT196 152 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 151
    simpa using h
  have hprev := st196_p151
  have hstep := st196_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p153 : ((2541421926423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT196 (i+1))
      = (∑ i ∈ Finset.range 152, stT196 (i+1)) + stT196 153 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 152
    simpa using h
  have hprev := st196_p152
  have hstep := st196_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p154 : ((13280033763497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT196 (i+1))
      = (∑ i ∈ Finset.range 153, stT196 (i+1)) + stT196 154 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 153
    simpa using h
  have hprev := st196_p153
  have hstep := st196_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p155 : ((12910760597477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT196 (i+1))
      = (∑ i ∈ Finset.range 154, stT196 (i+1)) + stT196 155 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 154
    simpa using h
  have hprev := st196_p154
  have hstep := st196_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p156 : ((1212125891571/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT196 (i+1))
      = (∑ i ∈ Finset.range 155, stT196 (i+1)) + stT196 156 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 155
    simpa using h
  have hprev := st196_p155
  have hstep := st196_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p157 : ((6000547872321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT196 (i+1))
      = (∑ i ∈ Finset.range 156, stT196 (i+1)) + stT196 157 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 156
    simpa using h
  have hprev := st196_p156
  have hstep := st196_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p158 : ((12707648214153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT196 (i+1))
      = (∑ i ∈ Finset.range 157, stT196 (i+1)) + stT196 158 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 157
    simpa using h
  have hprev := st196_p157
  have hstep := st196_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p159 : ((6641449033333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT196 (i+1))
      = (∑ i ∈ Finset.range 158, stT196 (i+1)) + stT196 159 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 158
    simpa using h
  have hprev := st196_p158
  have hstep := st196_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p160 : ((6481256624803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT196 (i+1))
      = (∑ i ∈ Finset.range 159, stT196 (i+1)) + stT196 160 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 159
    simpa using h
  have hprev := st196_p159
  have hstep := st196_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p161 : ((12176162101469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT196 (i+1))
      = (∑ i ∈ Finset.range 160, stT196 (i+1)) + stT196 161 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 160
    simpa using h
  have hprev := st196_p160
  have hstep := st196_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p162 : ((11951776464169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT196 (i+1))
      = (∑ i ∈ Finset.range 161, stT196 (i+1)) + stT196 162 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 161
    simpa using h
  have hprev := st196_p161
  have hstep := st196_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p163 : ((12573277608969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT196 (i+1))
      = (∑ i ∈ Finset.range 162, stT196 (i+1)) + stT196 163 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 162
    simpa using h
  have hprev := st196_p162
  have hstep := st196_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p164 : ((2648231114221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT196 (i+1))
      = (∑ i ∈ Finset.range 163, stT196 (i+1)) + stT196 164 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 163
    simpa using h
  have hprev := st196_p163
  have hstep := st196_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p165 : ((13113050446659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT196 (i+1))
      = (∑ i ∈ Finset.range 164, stT196 (i+1)) + stT196 165 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 164
    simpa using h
  have hprev := st196_p164
  have hstep := st196_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p166 : ((2471156019177/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT196 (i+1))
      = (∑ i ∈ Finset.range 165, stT196 (i+1)) + stT196 166 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 165
    simpa using h
  have hprev := st196_p165
  have hstep := st196_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p167 : ((11909371089997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT196 (i+1))
      = (∑ i ∈ Finset.range 166, stT196 (i+1)) + stT196 167 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 166
    simpa using h
  have hprev := st196_p166
  have hstep := st196_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p168 : ((2463213298241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT196 (i+1))
      = (∑ i ∈ Finset.range 167, stT196 (i+1)) + stT196 168 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 167
    simpa using h
  have hprev := st196_p167
  have hstep := st196_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p169 : ((2615376223001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT196 (i+1))
      = (∑ i ∈ Finset.range 168, stT196 (i+1)) + stT196 169 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 168
    simpa using h
  have hprev := st196_p168
  have hstep := st196_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p170 : ((2655801361513/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT196 (i+1))
      = (∑ i ∈ Finset.range 169, stT196 (i+1)) + stT196 170 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 169
    simpa using h
  have hprev := st196_p169
  have hstep := st196_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p171 : ((2537639733049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT196 (i+1))
      = (∑ i ∈ Finset.range 170, stT196 (i+1)) + stT196 171 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 170
    simpa using h
  have hprev := st196_p170
  have hstep := st196_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p172 : ((120032016413/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT196 (i+1))
      = (∑ i ∈ Finset.range 171, stT196 (i+1)) + stT196 172 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 171
    simpa using h
  have hprev := st196_p171
  have hstep := st196_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p173 : ((2403721155137/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT196 (i+1))
      = (∑ i ∈ Finset.range 172, stT196 (i+1)) + stT196 173 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 172
    simpa using h
  have hprev := st196_p172
  have hstep := st196_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p174 : ((12710531675559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT196 (i+1))
      = (∑ i ∈ Finset.range 173, stT196 (i+1)) + stT196 174 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 173
    simpa using h
  have hprev := st196_p173
  have hstep := st196_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p175 : ((2657496022971/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT196 (i+1))
      = (∑ i ∈ Finset.range 174, stT196 (i+1)) + stT196 175 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 174
    simpa using h
  have hprev := st196_p174
  have hstep := st196_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p176 : ((818881311503/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT196 (i+1))
      = (∑ i ∈ Finset.range 175, stT196 (i+1)) + stT196 176 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 175
    simpa using h
  have hprev := st196_p175
  have hstep := st196_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p177 : ((6183611614309/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT196 (i+1))
      = (∑ i ∈ Finset.range 176, stT196 (i+1)) + stT196 177 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 176
    simpa using h
  have hprev := st196_p176
  have hstep := st196_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p178 : ((5948397229729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT196 (i+1))
      = (∑ i ∈ Finset.range 177, stT196 (i+1)) + stT196 178 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 177
    simpa using h
  have hprev := st196_p177
  have hstep := st196_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p179 : ((12201265843883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT196 (i+1))
      = (∑ i ∈ Finset.range 178, stT196 (i+1)) + stT196 179 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 178
    simpa using h
  have hprev := st196_p178
  have hstep := st196_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p180 : ((12945274732753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT196 (i+1))
      = (∑ i ∈ Finset.range 179, stT196 (i+1)) + stT196 180 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 179
    simpa using h
  have hprev := st196_p179
  have hstep := st196_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p181 : ((2666011593523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT196 (i+1))
      = (∑ i ∈ Finset.range 180, stT196 (i+1)) + stT196 181 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 180
    simpa using h
  have hprev := st196_p180
  have hstep := st196_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p182 : ((2590331747523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT196 (i+1))
      = (∑ i ∈ Finset.range 181, stT196 (i+1)) + stT196 182 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 181
    simpa using h
  have hprev := st196_p181
  have hstep := st196_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p183 : ((12212958628347/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT196 (i+1))
      = (∑ i ∈ Finset.range 182, stT196 (i+1)) + stT196 183 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 182
    simpa using h
  have hprev := st196_p182
  have hstep := st196_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p184 : ((11883134560397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT196 (i+1))
      = (∑ i ∈ Finset.range 183, stT196 (i+1)) + stT196 184 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 183
    simpa using h
  have hprev := st196_p183
  have hstep := st196_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p185 : ((12297347511071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT196 (i+1))
      = (∑ i ∈ Finset.range 184, stT196 (i+1)) + stT196 185 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 184
    simpa using h
  have hprev := st196_p184
  have hstep := st196_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p186 : ((814246199931/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT196 (i+1))
      = (∑ i ∈ Finset.range 185, stT196 (i+1)) + stT196 186 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 185
    simpa using h
  have hprev := st196_p185
  have hstep := st196_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p187 : ((1667049904379/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT196 (i+1))
      = (∑ i ∈ Finset.range 186, stT196 (i+1)) + stT196 187 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 186
    simpa using h
  have hprev := st196_p186
  have hstep := st196_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p188 : ((807416211177/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT196 (i+1))
      = (∑ i ∈ Finset.range 187, stT196 (i+1)) + stT196 188 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 187
    simpa using h
  have hprev := st196_p187
  have hstep := st196_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p189 : ((38104654037/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT196 (i+1))
      = (∑ i ∈ Finset.range 188, stT196 (i+1)) + stT196 189 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 188
    simpa using h
  have hprev := st196_p188
  have hstep := st196_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p190 : ((1484111537477/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT196 (i+1))
      = (∑ i ∈ Finset.range 189, stT196 (i+1)) + stT196 190 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 189
    simpa using h
  have hprev := st196_p189
  have hstep := st196_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p191 : ((1533007050527/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT196 (i+1))
      = (∑ i ∈ Finset.range 190, stT196 (i+1)) + stT196 191 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 190
    simpa using h
  have hprev := st196_p190
  have hstep := st196_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p192 : ((1623187614673/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT196 (i+1))
      = (∑ i ∈ Finset.range 191, stT196 (i+1)) + stT196 192 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 191
    simpa using h
  have hprev := st196_p191
  have hstep := st196_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p193 : ((6674277004467/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT196 (i+1))
      = (∑ i ∈ Finset.range 192, stT196 (i+1)) + stT196 193 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 192
    simpa using h
  have hprev := st196_p192
  have hstep := st196_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p194 : ((650714835457/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT196 (i+1))
      = (∑ i ∈ Finset.range 193, stT196 (i+1)) + stT196 194 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 193
    simpa using h
  have hprev := st196_p193
  have hstep := st196_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p195 : ((1230037158881/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT196 (i+1))
      = (∑ i ∈ Finset.range 194, stT196 (i+1)) + stT196 195 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 194
    simpa using h
  have hprev := st196_p194
  have hstep := st196_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p196 : ((5934854993987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT196 (i+1))
      = (∑ i ∈ Finset.range 195, stT196 (i+1)) + stT196 196 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 195
    simpa using h
  have hprev := st196_p195
  have hstep := st196_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p197 : ((3028555463701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT196 (i+1))
      = (∑ i ∈ Finset.range 196, stT196 (i+1)) + stT196 197 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 196
    simpa using h
  have hprev := st196_p196
  have hstep := st196_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p198 : ((640322947181/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT196 (i+1))
      = (∑ i ∈ Finset.range 197, stT196 (i+1)) + stT196 198 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 197
    simpa using h
  have hprev := st196_p197
  have hstep := st196_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p199 : ((416267123481/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT196 (i+1))
      = (∑ i ∈ Finset.range 198, stT196 (i+1)) + stT196 199 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 198
    simpa using h
  have hprev := st196_p198
  have hstep := st196_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p200 : ((13200160863321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT196 (i+1))
      = (∑ i ∈ Finset.range 199, stT196 (i+1)) + stT196 200 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 199
    simpa using h
  have hprev := st196_p199
  have hstep := st196_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p201 : ((12556713912243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT196 (i+1))
      = (∑ i ∈ Finset.range 200, stT196 (i+1)) + stT196 201 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 200
    simpa using h
  have hprev := st196_p200
  have hstep := st196_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p202 : ((11957027486471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT196 (i+1))
      = (∑ i ∈ Finset.range 201, stT196 (i+1)) + stT196 202 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 201
    simpa using h
  have hprev := st196_p201
  have hstep := st196_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p203 : ((14900297417/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT196 (i+1))
      = (∑ i ∈ Finset.range 202, stT196 (i+1)) + stT196 203 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 202
    simpa using h
  have hprev := st196_p202
  have hstep := st196_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p204 : ((124732890217/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT196 (i+1))
      = (∑ i ∈ Finset.range 203, stT196 (i+1)) + stT196 204 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 203
    simpa using h
  have hprev := st196_p203
  have hstep := st196_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p205 : ((1314081978007/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT196 (i+1))
      = (∑ i ∈ Finset.range 204, stT196 (i+1)) + stT196 205 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 204
    simpa using h
  have hprev := st196_p204
  have hstep := st196_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p206 : ((13359044219733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT196 (i+1))
      = (∑ i ∈ Finset.range 205, stT196 (i+1)) + stT196 206 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 205
    simpa using h
  have hprev := st196_p205
  have hstep := st196_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p207 : ((6474615061701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT196 (i+1))
      = (∑ i ∈ Finset.range 206, stT196 (i+1)) + stT196 207 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 206
    simpa using h
  have hprev := st196_p206
  have hstep := st196_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p208 : ((6127912847493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT196 (i+1))
      = (∑ i ∈ Finset.range 207, stT196 (i+1)) + stT196 208 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 207
    simpa using h
  have hprev := st196_p207
  have hstep := st196_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p209 : ((2962567260049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT196 (i+1))
      = (∑ i ∈ Finset.range 208, stT196 (i+1)) + stT196 209 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 208
    simpa using h
  have hprev := st196_p208
  have hstep := st196_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p210 : ((6030088576143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT196 (i+1))
      = (∑ i ∈ Finset.range 209, stT196 (i+1)) + stT196 210 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 209
    simpa using h
  have hprev := st196_p209
  have hstep := st196_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p211 : ((6355652028981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT196 (i+1))
      = (∑ i ∈ Finset.range 210, stT196 (i+1)) + stT196 211 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 210
    simpa using h
  have hprev := st196_p210
  have hstep := st196_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p212 : ((3319898734713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT196 (i+1))
      = (∑ i ∈ Finset.range 211, stT196 (i+1)) + stT196 212 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 211
    simpa using h
  have hprev := st196_p211
  have hstep := st196_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p213 : ((332884060941/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT196 (i+1))
      = (∑ i ∈ Finset.range 212, stT196 (i+1)) + stT196 213 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 212
    simpa using h
  have hprev := st196_p212
  have hstep := st196_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p214 : ((1279471257867/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT196 (i+1))
      = (∑ i ∈ Finset.range 213, stT196 (i+1)) + stT196 214 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 213
    simpa using h
  have hprev := st196_p213
  have hstep := st196_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p215 : ((15159356873/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT196 (i+1))
      = (∑ i ∈ Finset.range 214, stT196 (i+1)) + stT196 215 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 214
    simpa using h
  have hprev := st196_p214
  have hstep := st196_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p216 : ((369685384101/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT196 (i+1))
      = (∑ i ∈ Finset.range 215, stT196 (i+1)) + stT196 216 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 215
    simpa using h
  have hprev := st196_p215
  have hstep := st196_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p217 : ((75792832663/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT196 (i+1))
      = (∑ i ∈ Finset.range 216, stT196 (i+1)) + stT196 217 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 216
    simpa using h
  have hprev := st196_p216
  have hstep := st196_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p218 : ((319705889357/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT196 (i+1))
      = (∑ i ∈ Finset.range 217, stT196 (i+1)) + stT196 218 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 217
    simpa using h
  have hprev := st196_p217
  have hstep := st196_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p219 : ((3328394461153/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT196 (i+1))
      = (∑ i ∈ Finset.range 218, stT196 (i+1)) + stT196 219 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 218
    simpa using h
  have hprev := st196_p218
  have hstep := st196_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p220 : ((3328001908203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT196 (i+1))
      = (∑ i ∈ Finset.range 219, stT196 (i+1)) + stT196 220 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 219
    simpa using h
  have hprev := st196_p219
  have hstep := st196_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p221 : ((12788760195013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT196 (i+1))
      = (∑ i ∈ Finset.range 220, stT196 (i+1)) + stT196 221 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 220
    simpa using h
  have hprev := st196_p220
  have hstep := st196_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p222 : ((3032914137859/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT196 (i+1))
      = (∑ i ∈ Finset.range 221, stT196 (i+1)) + stT196 222 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 221
    simpa using h
  have hprev := st196_p221
  have hstep := st196_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p223 : ((5909816901793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT196 (i+1))
      = (∑ i ∈ Finset.range 222, stT196 (i+1)) + stT196 223 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 222
    simpa using h
  have hprev := st196_p222
  have hstep := st196_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p224 : ((6037526329907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT196 (i+1))
      = (∑ i ∈ Finset.range 223, stT196 (i+1)) + stT196 224 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 223
    simpa using h
  have hprev := st196_p223
  have hstep := st196_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p225 : ((6355416012017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT196 (i+1))
      = (∑ i ∈ Finset.range 224, stT196 (i+1)) + stT196 225 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 224
    simpa using h
  have hprev := st196_p224
  have hstep := st196_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p226 : ((3318263817091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT196 (i+1))
      = (∑ i ∈ Finset.range 225, stT196 (i+1)) + stT196 226 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 225
    simpa using h
  have hprev := st196_p225
  have hstep := st196_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p227 : ((13366755035443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT196 (i+1))
      = (∑ i ∈ Finset.range 226, stT196 (i+1)) + stT196 227 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 226
    simpa using h
  have hprev := st196_p226
  have hstep := st196_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p228 : ((6465056234169/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT196 (i+1))
      = (∑ i ∈ Finset.range 227, stT196 (i+1)) + stT196 228 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 227
    simpa using h
  have hprev := st196_p227
  have hstep := st196_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p229 : ((490771025049/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT196 (i+1))
      = (∑ i ∈ Finset.range 228, stT196 (i+1)) + stT196 229 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 228
    simpa using h
  have hprev := st196_p228
  have hstep := st196_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p230 : ((5919731368521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT196 (i+1))
      = (∑ i ∈ Finset.range 229, stT196 (i+1)) + stT196 230 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 229
    simpa using h
  have hprev := st196_p229
  have hstep := st196_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p231 : ((11931489685461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT196 (i+1))
      = (∑ i ∈ Finset.range 230, stT196 (i+1)) + stT196 231 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 230
    simpa using h
  have hprev := st196_p230
  have hstep := st196_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p232 : ((12479259281277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT196 (i+1))
      = (∑ i ∈ Finset.range 231, stT196 (i+1)) + stT196 232 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 231
    simpa using h
  have hprev := st196_p231
  have hstep := st196_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p233 : ((3278114164253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT196 (i+1))
      = (∑ i ∈ Finset.range 232, stT196 (i+1)) + stT196 233 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 232
    simpa using h
  have hprev := st196_p232
  have hstep := st196_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p234 : ((3352433793323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT196 (i+1))
      = (∑ i ∈ Finset.range 233, stT196 (i+1)) + stT196 234 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 233
    simpa using h
  have hprev := st196_p233
  have hstep := st196_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p235 : ((6588830651797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT196 (i+1))
      = (∑ i ∈ Finset.range 234, stT196 (i+1)) + stT196 235 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 234
    simpa using h
  have hprev := st196_p234
  have hstep := st196_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p236 : ((3142970693341/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT196 (i+1))
      = (∑ i ∈ Finset.range 235, stT196 (i+1)) + stT196 236 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 235
    simpa using h
  have hprev := st196_p235
  have hstep := st196_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p237 : ((5994026902177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT196 (i+1))
      = (∑ i ∈ Finset.range 236, stT196 (i+1)) + stT196 237 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 236
    simpa using h
  have hprev := st196_p236
  have hstep := st196_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p238 : ((5900824890037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT196 (i+1))
      = (∑ i ∈ Finset.range 237, stT196 (i+1)) + stT196 238 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 237
    simpa using h
  have hprev := st196_p237
  have hstep := st196_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p239 : ((121287151699/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT196 (i+1))
      = (∑ i ∈ Finset.range 238, stT196 (i+1)) + stT196 239 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 238
    simpa using h
  have hprev := st196_p238
  have hstep := st196_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p240 : ((2551660779267/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT196 (i+1))
      = (∑ i ∈ Finset.range 239, stT196 (i+1)) + stT196 240 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 239
    simpa using h
  have hprev := st196_p239
  have hstep := st196_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p241 : ((13292549490523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT196 (i+1))
      = (∑ i ∈ Finset.range 240, stT196 (i+1)) + stT196 241 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 240
    simpa using h
  have hprev := st196_p240
  have hstep := st196_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p242 : ((13399039714363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT196 (i+1))
      = (∑ i ∈ Finset.range 241, stT196 (i+1)) + stT196 242 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 241
    simpa using h
  have hprev := st196_p241
  have hstep := st196_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p243 : ((13014997442701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT196 (i+1))
      = (∑ i ∈ Finset.range 242, stT196 (i+1)) + stT196 243 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 242
    simpa using h
  have hprev := st196_p242
  have hstep := st196_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p244 : ((12379703456101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT196 (i+1))
      = (∑ i ∈ Finset.range 243, stT196 (i+1)) + stT196 244 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 243
    simpa using h
  have hprev := st196_p243
  have hstep := st196_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p245 : ((5940954512567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT196 (i+1))
      = (∑ i ∈ Finset.range 244, stT196 (i+1)) + stT196 245 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 244
    simpa using h
  have hprev := st196_p244
  have hstep := st196_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p246 : ((11821471188573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT196 (i+1))
      = (∑ i ∈ Finset.range 245, stT196 (i+1)) + stT196 246 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 245
    simpa using h
  have hprev := st196_p245
  have hstep := st196_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p247 : ((12231465237961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT196 (i+1))
      = (∑ i ∈ Finset.range 246, stT196 (i+1)) + stT196 247 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 246
    simpa using h
  have hprev := st196_p246
  have hstep := st196_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p248 : ((12864471337961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT196 (i+1))
      = (∑ i ∈ Finset.range 247, stT196 (i+1)) + stT196 248 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 247
    simpa using h
  have hprev := st196_p247
  have hstep := st196_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p249 : ((2668998638937/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT196 (i+1))
      = (∑ i ∈ Finset.range 248, stT196 (i+1)) + stT196 249 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 248
    simpa using h
  have hprev := st196_p248
  have hstep := st196_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_p250 : ((1339242415741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT196 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT196 (i+1))
      = (∑ i ∈ Finset.range 249, stT196 (i+1)) + stT196 250 := by
    have h := Finset.sum_range_succ (fun i => stT196 (i+1)) 249
    simpa using h
  have hprev := st196_p249
  have hstep := st196_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st196_s250 :
    |Real.sin (((196 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))
      - ((49859/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 3739201/10000000) (δ := 2459/250000000) (ψ := 2793/1000000) 196 172
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 196`** (evaluated boundary). -/
theorem station_196_sign : 0 < hardyG ((((196:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 196 250 (by norm_num) (by norm_num)
    ((2793/1000000 : ℚ) : ℝ)
  have hchain := st196_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT196 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((196 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((2793/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st196_c250
  have hsinb := abs_le.mp st196_s250
  have hbdy_lo : ((-6182087506507/76832500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((196 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((2793/1000000 : ℚ) : ℝ))) / 2
          - ((((196:ℕ)):ℝ))
            * Real.sin (((196 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((2793/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((196:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((196:ℝ) * Real.log (250:ℝ) - ((2793/1000000 : ℚ) : ℝ))) / 2
        - ((196:ℝ)) * Real.sin ((196:ℝ) * Real.log (250:ℝ) - ((2793/1000000 : ℚ) : ℝ))
        ≥ ((-78197851/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((196:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-78197851/400000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-78197851/400000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-78197851/400000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((196:ℕ)):ℝ))+1) * (((((196:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((268398752171/312500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1339242415741/1000000000000 : ℚ) : ℝ) + ((-6182087506507/76832500000000 : ℚ) : ℝ)
      - ((268398752171/312500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((2793/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((196:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((2793/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((196:ℕ)):ℝ)))).re
      - Real.sin ((2793/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((196:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((196:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((196:ℕ)):ℝ))
      = (((((196:ℕ)):ℝ)) * (Real.log ((((196:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((196:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_196
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
  have hθwin : |(((2793/1000000 : ℚ) : ℝ) + ((38:ℤ)) * (2*Real.pi)) - theta ((((196:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((196:ℕ)):ℝ)))
    (φ := ((2793/1000000 : ℚ) : ℝ) + ((38:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((2793/1000000 : ℚ)) : ℝ) 38).1,
    (cos_sin_shift (((2793/1000000 : ℚ)) : ℝ) 38).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_196_sign
end AxiomAudit
