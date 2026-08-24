import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 339/2` (rung-199.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT339o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((339 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))

theorem st339o2_c1 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((790611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 65899/400000) (δ := 1/1000000000) (ψ := -65899/100000) 339 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t1 : ((790561/1000000 : ℚ) : ℝ) ≤ stT339o2 1 := by
  have hc : ((790561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((790561/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((790561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c2 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((13253/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1541361/5000000) (δ := 2147/250000000) (ψ := -65899/100000) 339 19
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t2 : ((93698708817/400000000000 : ℚ) : ℝ) ≤ stT339o2 2 := by
  have hc : ((13251/40000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93698708817/400000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((13251/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c3 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-25487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2027241/5000000) (δ := 8517/1000000000) (ψ := -65899/100000) 339 30
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t3 : ((-18411701067/625000000000 : ℚ) : ℝ) ≤ stT339o2 3 := by
  have hc : ((-3189/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18411701067/625000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-3189/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c4 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-199973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3906449/5000000) (δ := 539/62500000) (ψ := -65899/100000) 339 38
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t4 : ((-999915199983/2000000000000 : ℚ) : ℝ) ≤ stT339o2 4 := by
  have hc : ((-199983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-999915199983/2000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-199983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c5 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-990193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7503577/10000000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 44
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t5 : ((-553562671131/1250000000000 : ℚ) : ℝ) ≤ stT339o2 5 := by
  have hc : ((-990243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-553562671131/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-990243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c6 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-58219/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1384661/2000000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 48
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t6 : ((-1901526684291/5000000000000 : ℚ) : ℝ) ≤ stT339o2 6 := by
  have hc : ((-465777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1901526684291/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-465777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c7 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-811821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -393447/625000) (δ := 2133/250000000) (ψ := -65899/100000) 339 53
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t7 : ((-613716833159/2000000000000 : ℚ) : ℝ) ≤ stT339o2 7 := by
  have hc : ((-811871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-613716833159/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-811871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c8 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((300141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3164889/10000000) (δ := 4277/500000000) (ψ := -65899/100000) 339 56
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t8 : ((1060981633503/10000000000000 : ℚ) : ℝ) ≤ stT339o2 8 := by
  have hc : ((300091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1060981633503/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((300091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c9 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-181041/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1190309/2000000) (δ := 4289/500000000) (ψ := -65899/100000) 339 59
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t9 : ((-603511787369/2500000000000 : ℚ) : ℝ) ≤ stT339o2 9 := by
  have hc : ((-362107/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-603511787369/2500000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-362107/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c10 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((180141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3474167/10000000) (δ := 4303/500000000) (ψ := -65899/100000) 339 62
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t10 : ((569497627207/10000000000000 : ℚ) : ℝ) ≤ stT339o2 10 := by
  have hc : ((180091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569497627207/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((180091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c11 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((262861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -130481/400000) (δ := 1071/125000000) (ψ := -65899/100000) 339 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t11 : ((792404862643/10000000000000 : ℚ) : ℝ) ≤ stT339o2 11 := by
  have hc : ((262811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((792404862643/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((262811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c12 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((639267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2193129/10000000) (δ := 8483/1000000000) (ψ := -65899/100000) 339 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t12 : ((1845260313967/10000000000000 : ℚ) : ℝ) ≤ stT339o2 12 := by
  have hc : ((639217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1845260313967/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((639217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c13 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-75627/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4695297/10000000) (δ := 8647/1000000000) (ψ := -65899/100000) 339 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t13 : ((-419572457779/5000000000000 : ℚ) : ℝ) ≤ stT339o2 13 := by
  have hc : ((-151279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419572457779/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-151279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c14 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-74419/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 936527/2000000) (δ := 2123/250000000) (ψ := -65899/100000) 339 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t14 : ((-397853189019/5000000000000 : ℚ) : ℝ) ≤ stT339o2 14 := by
  have hc : ((-148863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397853189019/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-148863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c15 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((539477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 50049/200000) (δ := 4263/500000000) (ψ := -65899/100000) 339 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t15 : ((348198510219/2500000000000 : ℚ) : ℝ) ≤ stT339o2 15 := by
  have hc : ((539427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348198510219/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((539427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c16 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((81031/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1565287/10000000) (δ := 859/100000000) (ψ := -65899/100000) 339 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t16 : ((40513/200000 : ℚ) : ℝ) ≤ stT339o2 16 := by
  have hc : ((40513/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40513/200000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((40513/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c17 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-974799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -364577/500000) (δ := 8649/1000000000) (ψ := -65899/100000) 339 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t17 : ((-2364356846093/10000000000000 : ℚ) : ℝ) ≤ stT339o2 17 := by
  have hc : ((-974849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2364356846093/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-974849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c18 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((176603/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1221369/10000000) (δ := 8541/1000000000) (ψ := -65899/100000) 339 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t18 : ((208116793023/1000000000000 : ℚ) : ℝ) ≤ stT339o2 18 := by
  have hc : ((176593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208116793023/1000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((176593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c19 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-243521/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7283581/10000000) (δ := 4313/500000000) (ψ := -65899/100000) 339 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t19 : ((-558704327293/2500000000000 : ℚ) : ℝ) ≤ stT339o2 19 := by
  have hc : ((-487067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558704327293/2500000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-487067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c20 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((219107/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1256009/10000000) (δ := 857/100000000) (ψ := -65899/100000) 339 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t20 : ((979819962663/5000000000000 : ℚ) : ℝ) ≤ stT339o2 20 := by
  have hc : ((438189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((979819962663/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((438189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c21 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((86339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 29687/80000) (δ := 8563/1000000000) (ψ := -65899/100000) 339 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t21 : ((94148978721/5000000000000 : ℚ) : ℝ) ≤ stT339o2 21 := by
  have hc : ((86289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94148978721/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((86289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c22 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-124809/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3857881/5000000) (δ := 8497/1000000000) (ψ := -65899/100000) 339 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t22 : ((-133053555761/625000000000 : ℚ) : ℝ) ≤ stT339o2 22 := by
  have hc : ((-499261/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133053555761/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-499261/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c23 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-365983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2431857/5000000) (δ := 2153/250000000) (ψ := -65899/100000) 339 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t23 : ((-152646375957/2000000000000 : ℚ) : ℝ) ≤ stT339o2 23 := by
  have hc : ((-366033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152646375957/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-366033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c24 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((263887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2537047/10000000) (δ := 8519/1000000000) (ψ := -65899/100000) 339 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t24 : ((269302966371/2500000000000 : ℚ) : ℝ) ≤ stT339o2 24 := by
  have hc : ((131931/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((269302966371/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((131931/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c25 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((185831/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7396/78125) (δ := 8527/1000000000) (ψ := -65899/100000) 339 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t25 : ((185821/1000000 : ℚ) : ℝ) ≤ stT339o2 25 := by
  have hc : ((185821/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185821/1000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((185821/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c26 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((999903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -109/31250) (δ := 867/100000000) (ψ := -65899/100000) 339 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t26 : ((1960872709333/10000000000000 : ℚ) : ℝ) ≤ stT339o2 26 := by
  have hc : ((999853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1960872709333/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((999853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c27 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((49751/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 249609/10000000) (δ := 8613/1000000000) (ψ := -65899/100000) 339 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t27 : ((382963953/2000000000 : ℚ) : ℝ) ≤ stT339o2 27 := by
  have hc : ((99497/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((382963953/2000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((99497/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c28 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((999819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -47541/10000000) (δ := 4249/500000000) (ψ := -65899/100000) 339 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t28 : ((944692725559/5000000000000 : ℚ) : ℝ) ≤ stT339o2 28 := by
  have hc : ((999769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((944692725559/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((999769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c29 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((187583/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -442783/5000000) (δ := 4249/500000000) (ψ := -65899/100000) 339 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t29 : ((348314245069/2000000000000 : ℚ) : ℝ) ≤ stT339o2 29 := by
  have hc : ((187573/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348314245069/2000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((187573/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c30 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((628551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2227769/10000000) (δ := 8641/1000000000) (ψ := -65899/100000) 339 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t30 : ((1147480044241/10000000000000 : ℚ) : ℝ) ≤ stT339o2 30 := by
  have hc : ((628501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1147480044241/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((628501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c31 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-45593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1010253/2500000) (δ := 1073/125000000) (ψ := -65899/100000) 339 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t31 : ((-40988646361/5000000000000 : ℚ) : ℝ) ≤ stT339o2 31 := by
  have hc : ((-45643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40988646361/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-45643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c32 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-405947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6295463/10000000) (δ := 4313/500000000) (ψ := -65899/100000) 339 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t32 : ((-179415976131/1250000000000 : ℚ) : ℝ) ≤ stT339o2 32 := by
  have hc : ((-101493/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179415976131/1250000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-101493/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c33 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-225761/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3372001/5000000) (δ := 8527/1000000000) (ψ := -65899/100000) 339 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t33 : ((-786042632019/5000000000000 : ℚ) : ℝ) ≤ stT339o2 33 := by
  have hc : ((-451547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786042632019/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-451547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c34 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((24037/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 460781/1250000) (δ := 4317/500000000) (ψ := -65899/100000) 339 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t34 : ((16480662853/1000000000000 : ℚ) : ℝ) ≤ stT339o2 34 := by
  have hc : ((48049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16480662853/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((48049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c35 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((39781/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 261737/10000000) (δ := 4331/500000000) (ψ := -65899/100000) 339 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t35 : ((16809690483/100000000000 : ℚ) : ℝ) ≤ stT339o2 35 := by
  have hc : ((39779/40000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16809690483/100000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((39779/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c36 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((33299/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3508807/10000000) (δ := 1701/200000000) (ψ := -65899/100000) 339 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t36 : ((27740822237/1000000000000 : ℚ) : ℝ) ≤ stT339o2 36 := by
  have hc : ((33289/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27740822237/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((33289/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c37 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-497551/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1901611/2500000) (δ := 4249/500000000) (ψ := -65899/100000) 339 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t37 : ((-10225124603/62500000000 : ℚ) : ℝ) ≤ stT339o2 37 := by
  have hc : ((-62197/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10225124603/62500000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-62197/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c38 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((92979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1847103/5000000) (δ := 1711/200000000) (ψ := -65899/100000) 339 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t38 : ((75375362403/5000000000000 : ℚ) : ℝ) ≤ stT339o2 38 := by
  have hc : ((92929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75375362403/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((92929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c39 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((115003/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1006639/10000000) (δ := 2153/250000000) (ψ := -65899/100000) 339 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t39 : ((736568443347/5000000000000 : ℚ) : ℝ) ≤ stT339o2 39 := by
  have hc : ((459987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((736568443347/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((459987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c40 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-14673/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1197237/2000000) (δ := 4267/500000000) (ψ := -65899/100000) 339 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t40 : ((-11600816843/100000000000 : ℚ) : ℝ) ≤ stT339o2 40 := by
  have hc : ((-7337/10000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11600816843/100000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-7337/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c41 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-13647/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 559663/1250000) (δ := 4317/500000000) (ψ := -65899/100000) 339 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t41 : ((-85271675669/2500000000000 : ℚ) : ℝ) ≤ stT339o2 41 := by
  have hc : ((-109201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85271675669/2500000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-109201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c42 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((918027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1019301/10000000) (δ := 4263/500000000) (ψ := -65899/100000) 339 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t42 : ((1416468804241/10000000000000 : ℚ) : ℝ) ≤ stT339o2 42 := by
  have hc : ((917977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1416468804241/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((917977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c43 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-226283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1351243/2000000) (δ := 8569/1000000000) (ψ := -65899/100000) 339 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t43 : ((-345097469363/2500000000000 : ℚ) : ℝ) ≤ stT339o2 43 := by
  have hc : ((-452591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-345097469363/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-452591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c44 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((14709/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1492793/5000000) (δ := 4267/500000000) (ψ := -65899/100000) 339 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t44 : ((5542906523/100000000000 : ℚ) : ℝ) ≤ stT339o2 44 := by
  have hc : ((14707/40000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5542906523/100000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((14707/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c45 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((17931/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -399941/1250000) (δ := 8641/1000000000) (ψ := -65899/100000) 339 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t45 : ((213802243753/5000000000000 : ℚ) : ℝ) ≤ stT339o2 45 := by
  have hc : ((143423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213802243753/5000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((143423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c46 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-30697/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 611403/1000000) (δ := 4331/500000000) (ψ := -65899/100000) 339 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t46 : ((-2263160979/20000000000 : ℚ) : ℝ) ≤ stT339o2 46 := by
  have hc : ((-30699/40000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2263160979/20000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-30699/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c47 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((122697/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -240319/5000000) (δ := 2137/250000000) (ψ := -65899/100000) 339 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t47 : ((715850959187/5000000000000 : ℚ) : ℝ) ≤ stT339o2 47 := by
  have hc : ((490763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((715850959187/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((490763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c48 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-972583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7267223/10000000) (δ := 1711/200000000) (ψ := -65899/100000) 339 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t48 : ((-87742195563/625000000000 : ℚ) : ℝ) ≤ stT339o2 48 := by
  have hc : ((-972633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87742195563/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-972633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c49 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((52001/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1470163/10000000) (δ := 1711/200000000) (ψ := -65899/100000) 339 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t49 : ((594261250293/5000000000000 : ℚ) : ℝ) ≤ stT339o2 49 := by
  have hc : ((415983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594261250293/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((415983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c50 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-644179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -88701/156250) (δ := 849/100000000) (ψ := -65899/100000) 339 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t50 : ((-455538835503/5000000000000 : ℚ) : ℝ) ≤ stT339o2 50 := by
  have hc : ((-644229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-455538835503/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-644229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c51 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((466209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 339311/1250000) (δ := 8563/1000000000) (ψ := -65899/100000) 339 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t51 : ((16318828113/250000000000 : ℚ) : ℝ) ≤ stT339o2 51 := by
  have hc : ((466159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16318828113/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((466159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c52 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-328983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -37227/78125) (δ := 8633/1000000000) (ψ := -65899/100000) 339 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t52 : ((-456286841783/10000000000000 : ℚ) : ℝ) ≤ stT339o2 52 := by
  have hc : ((-329033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456286841783/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-329033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c53 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((24561/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3306619/10000000) (δ := 8533/1000000000) (ψ := -65899/100000) 339 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t53 : ((1686512219/50000000000 : ℚ) : ℝ) ≤ stT339o2 53 := by
  have hc : ((6139/25000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1686512219/50000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((6139/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c54 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-1757/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4480567/10000000) (δ := 67/7812500) (ψ := -65899/100000) 339 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t54 : ((-2989398909/100000000000 : ℚ) : ℝ) ≤ stT339o2 54 := by
  have hc : ((-8787/40000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2989398909/100000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-8787/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c55 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((50033/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 205929/625000) (δ := 4313/500000000) (ψ := -65899/100000) 339 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t55 : ((67450963177/2000000000000 : ℚ) : ℝ) ≤ stT339o2 55 := by
  have hc : ((50023/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67450963177/2000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((50023/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c56 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-333777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -29861/62500) (δ := 8669/1000000000) (ψ := -65899/100000) 339 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t56 : ((-446095356889/10000000000000 : ℚ) : ℝ) ≤ stT339o2 56 := by
  have hc : ((-333827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-446095356889/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-333827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c57 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((463391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1361223/5000000) (δ := 2121/250000000) (ψ := -65899/100000) 339 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t57 : ((153427495353/2500000000000 : ℚ) : ℝ) ≤ stT339o2 57 := by
  have hc : ((463341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153427495353/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((463341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c58 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-78161/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2807871/5000000) (δ := 8491/1000000000) (ψ := -65899/100000) 339 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t58 : ((-82110944097/1000000000000 : ℚ) : ℝ) ≤ stT339o2 58 := by
  have hc : ((-312669/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82110944097/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-312669/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c59 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((159071/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 162801/1000000) (δ := 8491/1000000000) (ψ := -65899/100000) 339 110
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t59 : ((207079766229/2000000000000 : ℚ) : ℝ) ≤ stT339o2 59 := by
  have hc : ((159061/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((207079766229/2000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((159061/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c60 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-468227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1391589/2000000) (δ := 1721/200000000) (ψ := -65899/100000) 339 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t60 : ((-30225549537/250000000000 : ℚ) : ℝ) ≤ stT339o2 60 := by
  have hc : ((-117063/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30225549537/250000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-117063/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c61 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((249957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 23173/5000000) (δ := 1711/200000000) (ψ := -65899/100000) 339 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t61 : ((40002617447/312500000000 : ℚ) : ℝ) ≤ stT339o2 61 := by
  have hc : ((499889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40002617447/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((499889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c62 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-233361/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6936733/10000000) (δ := 1701/200000000) (ψ := -65899/100000) 339 111
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t62 : ((-296384811747/2500000000000 : ℚ) : ℝ) ≤ stT339o2 62 := by
  have hc : ((-466747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296384811747/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-466747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c63 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((699267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1991061/10000000) (δ := 8597/1000000000) (ψ := -65899/100000) 339 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t63 : ((880930213177/10000000000000 : ℚ) : ℝ) ≤ stT339o2 63 := by
  have hc : ((699217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((880930213177/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((699217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c64 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-297541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4682281/10000000) (δ := 8647/1000000000) (ψ := -65899/100000) 339 112
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t64 : ((-371989047591/10000000000000 : ℚ) : ℝ) ≤ stT339o2 64 := by
  have hc : ((-297591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371989047591/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-297591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c65 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-209941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4455777/10000000) (δ := 8513/1000000000) (ψ := -65899/100000) 339 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t65 : ((-65115479217/2500000000000 : ℚ) : ℝ) ≤ stT339o2 65 := by
  have hc : ((-209991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65115479217/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-209991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c66 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((692729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1006913/5000000) (δ := 849/100000000) (ψ := -65899/100000) 339 113
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t66 : ((426314139303/5000000000000 : ℚ) : ℝ) ≤ stT339o2 66 := by
  have hc : ((692679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426314139303/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((692679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c67 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-97743/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7321827/10000000) (δ := 213/25000000) (ψ := -65899/100000) 339 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t67 : ((-5970912143/50000000000 : ℚ) : ℝ) ≤ stT339o2 67 := by
  have hc : ((-24437/25000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5970912143/50000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-24437/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c68 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((914077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -130491/1250000) (δ := 867/100000000) (ψ := -65899/100000) 339 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t68 : ((554210217153/5000000000000 : ℚ) : ℝ) ≤ stT339o2 68 := by
  have hc : ((914027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((554210217153/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((914027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c69 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-467207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5142313/10000000) (δ := 8483/1000000000) (ψ := -65899/100000) 339 114
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t69 : ((-562511544763/10000000000000 : ℚ) : ℝ) ≤ stT339o2 69 := by
  have hc : ((-467257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-562511544763/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-467257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c70 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-21489/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4468439/10000000) (δ := 4313/500000000) (ψ := -65899/100000) 339 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t70 : ((-12845126063/500000000000 : ℚ) : ℝ) ≤ stT339o2 70 := by
  have hc : ((-10747/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12845126063/500000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-10747/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c71 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((815667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 771143/5000000) (δ := 8627/1000000000) (ψ := -65899/100000) 339 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t71 : ((967958758877/10000000000000 : ℚ) : ℝ) ≤ stT339o2 71 := by
  have hc : ((815617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((967958758877/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((815617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c72 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-197633/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 373449/500000) (δ := 67/7812500) (ψ := -65899/100000) 339 115
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t72 : ((-14557790451/125000000000 : ℚ) : ℝ) ≤ stT339o2 72 := by
  have hc : ((-197643/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14557790451/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-197643/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c73 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((575461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -299259/1250000) (δ := 4267/500000000) (ψ := -65899/100000) 339 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t73 : ((673467363921/10000000000000 : ℚ) : ℝ) ≤ stT339o2 73 := by
  have hc : ((575411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((673467363921/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((575411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c74 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((4409/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3371301/10000000) (δ := 4267/500000000) (ψ := -65899/100000) 339 116
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t74 : ((160131069/6250000000 : ℚ) : ℝ) ≤ stT339o2 74 := by
  have hc : ((551/2500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160131069/6250000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((551/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c75 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-886003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -415539/625000) (δ := 8561/1000000000) (ψ := -65899/100000) 339 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t75 : ((-1023126285153/10000000000000 : ℚ) : ℝ) ≤ stT339o2 75 := by
  have hc : ((-886053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1023126285153/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-886053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c76 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((915363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -103597/1000000) (δ := 537/62500000) (ψ := -65899/100000) 339 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t76 : ((524967702707/5000000000000 : ℚ) : ℝ) ≤ stT339o2 76 := by
  have hc : ((915313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((524967702707/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((915313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c77 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-457/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1125833/2500000) (δ := 8511/1000000000) (ψ := -65899/100000) 339 117
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t77 : ((-2604569513/100000000000 : ℚ) : ℝ) ≤ stT339o2 77 := by
  have hc : ((-4571/20000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2604569513/100000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-4571/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c78 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-331167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1147363/2000000) (δ := 8649/1000000000) (ψ := -65899/100000) 339 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t78 : ((-23437588461/312500000000 : ℚ) : ℝ) ≤ stT339o2 78 := by
  have hc : ((-41399/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23437588461/312500000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-41399/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c79 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((990839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -42333/1250000) (δ := 8549/1000000000) (ψ := -65899/100000) 339 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t79 : ((1114723823643/10000000000000 : ℚ) : ℝ) ≤ stT339o2 79 := by
  have hc : ((990789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1114723823643/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((990789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c80 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-41309/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2495801/5000000) (δ := 2151/250000000) (ψ := -65899/100000) 339 118
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t80 : ((-11547614169/250000000000 : ℚ) : ℝ) ≤ stT339o2 80 := by
  have hc : ((-20657/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11547614169/250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-20657/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c81 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-286489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5452327/10000000) (δ := 8647/1000000000) (ψ := -65899/100000) 339 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t81 : ((-19896821473/312500000000 : ℚ) : ℝ) ≤ stT339o2 81 := by
  have hc : ((-143257/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19896821473/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-143257/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c82 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((994889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -31609/1250000) (δ := 8597/1000000000) (ψ := -65899/100000) 339 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t82 : ((219723126057/2000000000000 : ℚ) : ℝ) ≤ stT339o2 82 := by
  have hc : ((994839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219723126057/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((994839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c83 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-93341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1220893/2500000) (δ := 541/62500000) (ψ := -65899/100000) 339 119
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t83 : ((-204937631601/5000000000000 : ℚ) : ℝ) ≤ stT339o2 83 := by
  have hc : ((-186707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204937631601/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-186707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c84 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-333063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2874749/5000000) (δ := 17013/1000000000) (ψ := -65899/100000) 339 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t84 : ((-1135715581/15625000000 : ℚ) : ℝ) ≤ stT339o2 84 := by
  have hc : ((-10409/15625 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1135715581/15625000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-10409/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c85 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((957133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -14693/200000) (δ := 849/100000000) (ψ := -65899/100000) 339 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t85 : ((259525497529/2500000000000 : ℚ) : ℝ) ≤ stT339o2 85 := by
  have hc : ((957083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259525497529/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((957083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c86 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-117543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 422153/1000000) (δ := 849/100000000) (ψ := -65899/100000) 339 120
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t86 : ((-15850478063/1250000000000 : ℚ) : ℝ) ≤ stT339o2 86 := by
  have hc : ((-117593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15850478063/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-117593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c87 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-874403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3293751/5000000) (δ := 8533/1000000000) (ψ := -65899/100000) 339 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t87 : ((-937512429189/10000000000000 : ℚ) : ℝ) ≤ stT339o2 87 := by
  have hc : ((-874453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-937512429189/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-874453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c88 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((383117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -174459/1000000) (δ := 857/100000000) (ψ := -65899/100000) 339 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t88 : ((102094305319/1250000000000 : ℚ) : ℝ) ≤ stT339o2 88 := by
  have hc : ((95773/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102094305319/1250000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((95773/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c89 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((346059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3043573/10000000) (δ := 213/25000000) (ψ := -65899/100000) 339 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t89 : ((366768501973/10000000000000 : ℚ) : ℝ) ≤ stT339o2 89 := by
  have hc : ((346009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366768501973/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((346009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c90 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-999541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7778259/10000000) (δ := 857/100000000) (ψ := -65899/100000) 339 121
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t90 : ((-1053661875963/10000000000000 : ℚ) : ℝ) ≤ stT339o2 90 := by
  have hc : ((-999591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1053661875963/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-999591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c91 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((268527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3247331/10000000) (δ := 8563/500000000) (ψ := -65899/100000) 339 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t91 : ((70360035867/2500000000000 : ℚ) : ℝ) ≤ stT339o2 91 := by
  have hc : ((268477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70360035867/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((268477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c92 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((212667/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 691927/5000000) (δ := 4313/500000000) (ψ := -65899/100000) 339 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t92 : ((110853813687/1250000000000 : ℚ) : ℝ) ≤ stT339o2 92 := by
  have hc : ((425309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110853813687/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((425309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c93 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-363929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5964973/10000000) (δ := 67/7812500) (ψ := -65899/100000) 339 122
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t93 : ((-23587676763/312500000000 : ℚ) : ℝ) ≤ stT339o2 93 := by
  have hc : ((-181977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23587676763/312500000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-181977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c94 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-491269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5210857/10000000) (δ := 4309/500000000) (ψ := -65899/100000) 339 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t94 : ((-253378612809/5000000000000 : ℚ) : ℝ) ≤ stT339o2 94 := by
  have hc : ((-491319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253378612809/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-491319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c95 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((19161/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -181673/2500000) (δ := 1071/125000000) (ψ := -65899/100000) 339 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t95 : ((245721731/2500000000 : ℚ) : ℝ) ≤ stT339o2 95 := by
  have hc : ((479/500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((245721731/2500000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((479/500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c96 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((86479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1855261/5000000) (δ := 1727/200000000) (ψ := -65899/100000) 339 123
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t96 : ((4410558299/500000000000 : ℚ) : ℝ) ≤ stT339o2 96 := by
  have hc : ((86429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4410558299/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((86429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c97 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-995093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1521241/2000000) (δ := 4271/500000000) (ψ := -65899/100000) 339 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t97 : ((-1010415459621/10000000000000 : ℚ) : ℝ) ≤ stT339o2 97 := by
  have hc : ((-995143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1010415459621/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-995143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c98 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((263637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3260013/10000000) (δ := 537/62500000) (ψ := -65899/100000) 339 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t98 : ((33282866903/1250000000000 : ℚ) : ℝ) ≤ stT339o2 98 := by
  have hc : ((263587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33282866903/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((263587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c99 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((457189/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 521033/5000000) (δ := 8561/1000000000) (ψ := -65899/100000) 339 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t99 : ((114866683767/1250000000000 : ℚ) : ℝ) ≤ stT339o2 99 := by
  have hc : ((114291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114866683767/1250000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((114291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c100 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-522309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5300881/10000000) (δ := 4271/500000000) (ψ := -65899/100000) 339 124
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t100 : ((-522359/10000000 : ℚ) : ℝ) ≤ stT339o2 100 := by
  have hc : ((-522359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522359/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-522359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c101 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-786699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -30953/50000) (δ := 8649/1000000000) (ψ := -65899/100000) 339 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t101 : ((-391422575731/5000000000000 : ℚ) : ℝ) ≤ stT339o2 101 := by
  have hc : ((-786749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391422575731/5000000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-786749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c102 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((692191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -251961/1250000) (δ := 8599/1000000000) (ψ := -65899/100000) 339 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t102 : ((685321334727/10000000000000 : ℚ) : ℝ) ≤ stT339o2 102 := by
  have hc : ((692141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((685321334727/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((692141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c103 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((661947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2118459/10000000) (δ := 1063/125000000) (ψ := -65899/100000) 339 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t103 : ((652186309113/10000000000000 : ℚ) : ℝ) ≤ stT339o2 103 := by
  have hc : ((661897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((652186309113/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((661897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c104 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-792123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6212689/10000000) (δ := 4277/500000000) (ψ := -65899/100000) 339 125
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t104 : ((-776789792513/10000000000000 : ℚ) : ℝ) ≤ stT339o2 104 := by
  have hc : ((-792173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-776789792513/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-792173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c105 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-113799/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2720099/5000000) (δ := 541/62500000) (ψ := -65899/100000) 339 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t105 : ((-111066316909/2000000000000 : ℚ) : ℝ) ≤ stT339o2 105 := by
  have hc : ((-113809/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111066316909/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-113809/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c106 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((842203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1423599/10000000) (δ := 4303/500000000) (ψ := -65899/100000) 339 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t106 : ((163594115321/2000000000000 : ℚ) : ℝ) ≤ stT339o2 106 := by
  have hc : ((842153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163594115321/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((842153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c107 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((521549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 39927/156250) (δ := 8647/1000000000) (ψ := -65899/100000) 339 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t107 : ((31509491079/625000000000 : ℚ) : ℝ) ≤ stT339o2 107 := by
  have hc : ((521499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31509491079/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((521499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c108 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-171263/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 324861/500000) (δ := 8647/1000000000) (ψ := -65899/100000) 339 126
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t108 : ((-164807615523/2000000000000 : ℚ) : ℝ) ≤ stT339o2 108 := by
  have hc : ((-171273/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164807615523/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-171273/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c109 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-65473/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5305209/10000000) (δ := 27/3125000) (ψ := -65899/100000) 339 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t109 : ((-250871174359/5000000000000 : ℚ) : ℝ) ≤ stT339o2 109 := by
  have hc : ((-261917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250871174359/5000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-261917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c110 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((209917/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -89707/625000) (δ := 859/100000000) (ψ := -65899/100000) 339 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t110 : ((200135964379/2500000000000 : ℚ) : ℝ) ≤ stT339o2 110 := by
  have hc : ((419809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200135964379/2500000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((419809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c111 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((573657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2399583/10000000) (δ := 27/3125000) (ψ := -65899/100000) 339 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t111 : ((544443099299/10000000000000 : ℚ) : ℝ) ≤ stT339o2 111 := by
  have hc : ((573607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544443099299/10000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((573607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c112 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-394511/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1550007/2500000) (δ := 8613/1000000000) (ψ := -65899/100000) 339 127
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t112 : ((-2912514069/39062500000 : ℚ) : ℝ) ≤ stT339o2 112 := by
  have hc : ((-49317/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2912514069/39062500000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-49317/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c113 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-331827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2870611/5000000) (δ := 8533/1000000000) (ψ := -65899/100000) 339 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t113 : ((-78045036323/1250000000000 : ℚ) : ℝ) ≤ stT339o2 113 := by
  have hc : ((-82963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78045036323/1250000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-82963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c114 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((138897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -200773/1000000) (δ := 213/25000000) (ψ := -65899/100000) 339 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t114 : ((26015896179/400000000000 : ℚ) : ℝ) ≤ stT339o2 114 := by
  have hc : ((138887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26015896179/400000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((138887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c115 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((389643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 67727/400000) (δ := 8583/1000000000) (ψ := -65899/100000) 339 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t115 : ((22707521467/312500000000 : ℚ) : ℝ) ≤ stT339o2 115 := by
  have hc : ((194809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22707521467/312500000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((194809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c116 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-542999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5362003/10000000) (δ := 857/100000000) (ψ := -65899/100000) 339 128
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t116 : ((-504208506373/10000000000000 : ℚ) : ℝ) ≤ stT339o2 116 := by
  have hc : ((-543049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504208506373/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-543049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c117 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-896867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -268343/400000) (δ := 4289/500000000) (ψ := -65899/100000) 339 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t117 : ((-829200663417/10000000000000 : ℚ) : ℝ) ≤ stT339o2 117 := by
  have hc : ((-896917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-829200663417/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-896917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c118 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((323977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1551083/5000000) (δ := 533/62500000) (ψ := -65899/100000) 339 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t118 : ((149099387049/5000000000000 : ℚ) : ℝ) ≤ stT339o2 118 := by
  have hc : ((323927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149099387049/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((323927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c119 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((982097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 18951/400000) (δ := 69/8000000) (ψ := -65899/100000) 339 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t119 : ((450120260403/5000000000000 : ℚ) : ℝ) ≤ stT339o2 119 := by
  have hc : ((982047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450120260403/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((982047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c120 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-9283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2009921/5000000) (δ := 347/40000000) (ψ := -65899/100000) 339 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t120 : ((-16971184761/5000000000000 : ℚ) : ℝ) ≤ stT339o2 120 := by
  have hc : ((-18591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16971184761/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-18591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c121 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-198389/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7536459/10000000) (δ := 4239/500000000) (ψ := -65899/100000) 339 129
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t121 : ((-180362745309/2000000000000 : ℚ) : ℝ) ≤ stT339o2 121 := by
  have hc : ((-198399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180362745309/2000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-198399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c122 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-298133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -468383/1000000) (δ := 4259/500000000) (ψ := -65899/100000) 339 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t122 : ((-134981182257/5000000000000 : ℚ) : ℝ) ≤ stT339o2 122 := by
  have hc : ((-298183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134981182257/5000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-298183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c123 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((441201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -153079/1250000) (δ := 2167/250000000) (ψ := -65899/100000) 339 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t123 : ((49724340343/625000000000 : ℚ) : ℝ) ≤ stT339o2 123 := by
  have hc : ((55147/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49724340343/625000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((55147/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c124 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((635127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2206557/10000000) (δ := 1697/200000000) (ψ := -65899/100000) 339 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t124 : ((285157829001/5000000000000 : ℚ) : ℝ) ≤ stT339o2 124 := by
  have hc : ((635077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285157829001/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((635077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c125 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-623557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2805101/5000000) (δ := 1717/200000000) (ψ := -65899/100000) 339 130
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t125 : ((-139442890449/2500000000000 : ℚ) : ℝ) ≤ stT339o2 125 := by
  have hc : ((-623607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139442890449/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-623607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c126 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-179819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6721237/10000000) (δ := 8561/1000000000) (ψ := -65899/100000) 339 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t126 : ((-160204441059/2000000000000 : ℚ) : ℝ) ≤ stT339o2 126 := by
  have hc : ((-179829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160204441059/2000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-179829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c127 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((27549/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3371451/10000000) (δ := 8611/1000000000) (ψ := -65899/100000) 339 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t127 : ((24440224469/1250000000000 : ℚ) : ℝ) ≤ stT339o2 127 := by
  have hc : ((110171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24440224469/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((110171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c128 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((124977/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -9579/2000000) (δ := 8611/1000000000) (ψ := -65899/100000) 339 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t128 : ((441838085689/5000000000000 : ℚ) : ℝ) ≤ stT339o2 128 := by
  have hc : ((499883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441838085689/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((499883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c129 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((267571/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3249813/10000000) (δ := 4321/500000000) (ψ := -65899/100000) 339 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t129 : ((4710777289/200000000000 : ℚ) : ℝ) ≤ stT339o2 129 := by
  have hc : ((267521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4710777289/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((267521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c130 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-430697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 652201/1000000) (δ := 8511/1000000000) (ψ := -65899/100000) 339 131
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t130 : ((-188884303299/2500000000000 : ℚ) : ℝ) ≤ stT339o2 130 := by
  have hc : ((-215361/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188884303299/2500000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-215361/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c131 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-720639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5938799/10000000) (δ := 8599/1000000000) (ψ := -65899/100000) 339 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t131 : ((-125933916549/2000000000000 : ℚ) : ℝ) ≤ stT339o2 131 := by
  have hc : ((-720689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125933916549/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-720689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c132 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((9311/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -54327/200000) (δ := 8499/1000000000) (ψ := -65899/100000) 339 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t132 : ((202582807/5000000000 : ℚ) : ℝ) ≤ stT339o2 132 := by
  have hc : ((931/2000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202582807/5000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((931/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c133 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((981489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 30111/625000) (δ := 8499/1000000000) (ψ := -65899/100000) 339 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t133 : ((851014589851/10000000000000 : ℚ) : ℝ) ≤ stT339o2 133 := by
  have hc : ((981439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((851014589851/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((981439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c134 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((6763/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3655939/10000000) (δ := 16999/1000000000) (ψ := -65899/100000) 339 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t134 : ((11679279393/1250000000000 : ℚ) : ℝ) ≤ stT339o2 134 := by
  have hc : ((54079/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11679279393/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((54079/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c135 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-913499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6806499/10000000) (δ := 8499/1000000000) (ψ := -65899/100000) 339 132
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t135 : ((-786257822987/10000000000000 : ℚ) : ℝ) ≤ stT339o2 135 := by
  have hc : ((-913549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786257822987/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-913549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c136 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-673447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5774147/10000000) (δ := 8497/1000000000) (ψ := -65899/100000) 339 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t136 : ((-577518963021/10000000000000 : ℚ) : ℝ) ≤ stT339o2 136 := by
  have hc : ((-673497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-577518963021/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-673497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c137 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((481979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -166857/625000) (δ := 4253/500000000) (ψ := -65899/100000) 339 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t137 : ((411739414653/10000000000000 : ℚ) : ℝ) ≤ stT339o2 137 := by
  have hc : ((481929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411739414653/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((481929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c138 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((197289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 82419/2000000) (δ := 541/62500000) (ψ := -65899/100000) 339 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t138 : ((20991866553/250000000000 : ℚ) : ℝ) ≤ stT339o2 138 := by
  have hc : ((197279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20991866553/250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((197279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c139 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((22639/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3471697/10000000) (δ := 4303/500000000) (ψ := -65899/100000) 339 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t139 : ((19196826957/1250000000000 : ℚ) : ℝ) ≤ stT339o2 139 := by
  have hc : ((90531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19196826957/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((90531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c140 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-858811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6509349/10000000) (δ := 541/62500000) (ψ := -65899/100000) 339 133
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t140 : ((-145174133691/2000000000000 : ℚ) : ℝ) ≤ stT339o2 140 := by
  have hc : ((-858861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145174133691/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-858861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c141 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-196181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -772827/1250000) (δ := 1083/125000000) (ψ := -65899/100000) 339 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t141 : ((-41306187103/625000000000 : ℚ) : ℝ) ≤ stT339o2 141 := by
  have hc : ((-392387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41306187103/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-392387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c142 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((36419/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -318789/1000000) (δ := 1083/125000000) (ψ := -65899/100000) 339 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t142 : ((122227551831/5000000000000 : ℚ) : ℝ) ≤ stT339o2 142 := by
  have hc : ((145651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122227551831/5000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((145651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c143 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((249083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -107091/5000000) (δ := 1083/125000000) (ψ := -65899/100000) 339 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t143 : ((208283213061/2500000000000 : ℚ) : ℝ) ≤ stT339o2 143 := by
  have hc : ((498141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208283213061/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((498141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c144 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((228799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1369381/5000000) (δ := 2141/250000000) (ψ := -65899/100000) 339 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t144 : ((95322461871/2500000000000 : ℚ) : ℝ) ≤ stT339o2 144 := by
  have hc : ((114387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95322461871/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((114387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c145 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-321241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1417831/2500000) (δ := 4307/500000000) (ψ := -65899/100000) 339 134
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t145 : ((-26679695603/500000000000 : ℚ) : ℝ) ≤ stT339o2 145 := by
  have hc : ((-160633/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26679695603/500000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-160633/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c146 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-957701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -890531/1250000) (δ := 8571/1000000000) (ψ := -65899/100000) 339 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t146 : ((-396320237053/5000000000000 : ℚ) : ℝ) ≤ stT339o2 146 := by
  have hc : ((-957751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-396320237053/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-957751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c147 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-121611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4231773/10000000) (δ := 8521/1000000000) (ψ := -65899/100000) 339 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t147 : ((-100344411207/10000000000000 : ℚ) : ℝ) ≤ stT339o2 147 := by
  have hc : ((-121661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100344411207/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-121661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c148 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((427939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -10871/80000) (δ := 8571/1000000000) (ψ := -65899/100000) 339 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t148 : ((87935685129/1250000000000 : ℚ) : ℝ) ≤ stT339o2 148 := by
  have hc : ((213957/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87935685129/1250000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((213957/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c149 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((826531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 14947/100000) (δ := 8621/1000000000) (ψ := -65899/100000) 339 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t149 : ((677078856111/10000000000000 : ℚ) : ℝ) ≤ stT339o2 149 := by
  have hc : ((826481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((677078856111/10000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((826481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c150 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-160159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4329121/10000000) (δ := 4241/500000000) (ψ := -65899/100000) 339 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t150 : ((-130810167873/10000000000000 : ℚ) : ℝ) ≤ stT339o2 150 := by
  have hc : ((-160209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130810167873/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-160209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c151 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-960031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 714477/1000000) (δ := 4291/500000000) (ψ := -65899/100000) 339 135
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t151 : ((-781303356909/10000000000000 : ℚ) : ℝ) ≤ stT339o2 151 := by
  have hc : ((-960081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-781303356909/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-960081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c152 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-335539/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2883073/5000000) (δ := 2157/250000000) (ψ := -65899/100000) 339 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t152 : ((-17011165307/312500000000 : ℚ) : ℝ) ≤ stT339o2 152 := by
  have hc : ((-83891/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17011165307/312500000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-83891/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c153 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((367033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -373431/1250000) (δ := 533/62500000) (ψ := -65899/100000) 339 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t153 : ((74172035079/2500000000000 : ℚ) : ℝ) ≤ stT339o2 153 := by
  have hc : ((366983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74172035079/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((366983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c154 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((497943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -56711/2500000) (δ := 4239/500000000) (ψ := -65899/100000) 339 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t154 : ((100308319649/1250000000000 : ℚ) : ℝ) ≤ stT339o2 154 := by
  have hc : ((248959/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100308319649/1250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((248959/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c155 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((534947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1257939/5000000) (δ := 533/62500000) (ψ := -65899/100000) 339 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t155 : ((429639433443/10000000000000 : ℚ) : ℝ) ≤ stT339o2 155 := by
  have hc : ((534897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429639433443/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((534897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c156 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-250863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1310243/2500000) (δ := 4289/500000000) (ψ := -65899/100000) 339 136
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t156 : ((-25108902401/625000000000 : ℚ) : ℝ) ≤ stT339o2 156 := by
  have hc : ((-31361/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25108902401/625000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-31361/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c157 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-999283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3879657/5000000) (δ := 1071/125000000) (ψ := -65899/100000) 339 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t157 : ((-797554675971/10000000000000 : ℚ) : ℝ) ≤ stT339o2 157 := by
  have hc : ((-999333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-797554675971/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-999333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c158 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-6891/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -126721/250000) (δ := 1717/200000000) (ψ := -65899/100000) 339 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t158 : ((-87724987323/2500000000000 : ℚ) : ℝ) ≤ stT339o2 158 := by
  have hc : ((-220537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87724987323/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-220537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c159 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((575053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2395317/10000000) (δ := 1071/125000000) (ψ := -65899/100000) 339 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t159 : ((456006704153/10000000000000 : ℚ) : ℝ) ≤ stT339o2 159 := by
  have hc : ((575003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456006704153/10000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((575003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c160 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((994537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 130713/5000000) (δ := 1071/125000000) (ψ := -65899/100000) 339 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t160 : ((786210593103/10000000000000 : ℚ) : ℝ) ≤ stT339o2 160 := by
  have hc : ((994487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((786210593103/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((994487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c161 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((12461/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2901601/10000000) (δ := 1727/200000000) (ψ := -65899/100000) 339 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t161 : ((15711051661/500000000000 : ℚ) : ℝ) ≤ stT339o2 161 := by
  have hc : ((199351/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15711051661/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((199351/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c162 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-119341/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5525461/10000000) (δ := 1727/200000000) (ψ := -65899/100000) 339 137
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t162 : ((-3750843877/80000000000 : ℚ) : ℝ) ≤ stT339o2 162 := by
  have hc : ((-119351/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3750843877/80000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-119351/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c163 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-993771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1893697/2500000) (δ := 8661/1000000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t163 : ((-778421230281/10000000000000 : ℚ) : ℝ) ≤ stT339o2 163 := by
  have hc : ((-993821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-778421230281/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-993821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c164 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-102493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -622881/1250000) (δ := 8561/1000000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t164 : ((-160086734559/5000000000000 : ℚ) : ℝ) ≤ stT339o2 164 := by
  have hc : ((-205011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160086734559/5000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-205011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c165 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((357/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -75221/312500) (δ := 8661/1000000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t165 : ((4446391327/100000000000 : ℚ) : ℝ) ≤ stT339o2 165 := by
  have hc : ((11423/20000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4446391327/100000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((11423/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c166 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((998119/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 153353/10000000) (δ := 8511/1000000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t166 : ((15493025087/200000000000 : ℚ) : ℝ) ≤ stT339o2 166 := by
  have hc : ((998069/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15493025087/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((998069/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c167 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((471879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1349219/5000000) (δ := 2123/250000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t167 : ((365112132267/10000000000000 : ℚ) : ℝ) ≤ stT339o2 167 := by
  have hc : ((471829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365112132267/10000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((471829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c168 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-497323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1307067/2500000) (δ := 4271/500000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t168 : ((-383731724841/10000000000000 : ℚ) : ℝ) ≤ stT339o2 168 := by
  have hc : ((-497373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383731724841/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-497373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c169 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-999017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7743139/10000000) (δ := 8611/1000000000) (ψ := -65899/100000) 339 138
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t169 : ((-768513307477/10000000000000 : ℚ) : ℝ) ≤ stT339o2 169 := by
  have hc : ((-999067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-768513307477/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-999067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c170 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-144267/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2732413/5000000) (δ := 8499/1000000000) (ψ := -65899/100000) 339 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t170 : ((-44262930687/1000000000000 : ℚ) : ℝ) ≤ stT339o2 170 := by
  have hc : ((-288559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44262930687/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-288559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c171 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((46249/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -297949/1000000) (δ := 1063/125000000) (ψ := -65899/100000) 339 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t171 : ((141450838149/5000000000000 : ℚ) : ℝ) ≤ stT339o2 171 := by
  have hc : ((184971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141450838149/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((184971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c172 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((489687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -254323/5000000) (δ := 8499/1000000000) (ψ := -65899/100000) 339 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t172 : ((46670419713/625000000000 : ℚ) : ℝ) ≤ stT339o2 172 := by
  have hc : ((244831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46670419713/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((244831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c173 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((711511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 15583/80000) (δ := 1063/125000000) (ψ := -65899/100000) 339 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t173 : ((108182625277/2000000000000 : ℚ) : ℝ) ≤ stT339o2 173 := by
  have hc : ((711461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108182625277/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((711461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c174 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-92121/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4390243/10000000) (δ := 8499/1000000000) (ψ := -65899/100000) 339 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t174 : ((-34927895227/2500000000000 : ℚ) : ℝ) ≤ stT339o2 174 := by
  have hc : ((-46073/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34927895227/2500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-46073/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c175 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-457731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6818627/10000000) (δ := 1063/125000000) (ψ := -65899/100000) 339 139
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t175 : ((-86507758831/1250000000000 : ℚ) : ℝ) ≤ stT339o2 175 := by
  have hc : ((-114439/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86507758831/1250000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-114439/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c176 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-851651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6474809/10000000) (δ := 2149/250000000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t176 : ((-641994328079/10000000000000 : ℚ) : ℝ) ≤ stT339o2 176 := by
  have hc : ((-851701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641994328079/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-851701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c177 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-2937/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2036963/5000000) (δ := 531/62500000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t177 : ((-4418932713/1000000000000 : ℚ) : ℝ) ≤ stT339o2 177 := by
  have hc : ((-5879/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4418932713/1000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-5879/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c178 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((780931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1686603/10000000) (δ := 8557/1000000000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t178 : ((585294516811/10000000000000 : ℚ) : ℝ) ≤ stT339o2 178 := by
  have hc : ((780881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((585294516811/10000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((780881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c179 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((962439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 687371/10000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t179 : ((143864644443/2000000000000 : ℚ) : ℝ) ≤ stT339o2 179 := by
  have hc : ((962389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143864644443/2000000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((962389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c180 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((172183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3048083/10000000) (δ := 8607/1000000000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t180 : ((12831882609/500000000000 : ℚ) : ℝ) ≤ stT339o2 180 := by
  have hc : ((86079/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12831882609/500000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((86079/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c181 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-277141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2697871/5000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t181 : ((-20601610197/500000000000 : ℚ) : ℝ) ≤ stT339o2 181 := by
  have hc : ((-138583/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20601610197/500000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-138583/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c182 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-998779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1546087/2000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 140
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t182 : ((-592305597/8000000000 : ℚ) : ℝ) ≤ stT339o2 182 := by
  have hc : ((-998829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592305597/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-998829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c183 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-637647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -565559/1000000) (δ := 8589/1000000000) (ψ := -65899/100000) 339 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t183 : ((-235699825867/5000000000000 : ℚ) : ℝ) ≤ stT339o2 183 := by
  have hc : ((-637697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-235699825867/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-637697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c184 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((46037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1673161/5000000) (δ := 8589/1000000000) (ψ := -65899/100000) 339 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t184 : ((33931518643/2000000000000 : ℚ) : ℝ) ≤ stT339o2 184 := by
  have hc : ((46027/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33931518643/2000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((46027/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c185 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((456581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -524777/5000000) (δ := 4307/500000000) (ψ := -65899/100000) 339 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t185 : ((41958295373/625000000000 : ℚ) : ℝ) ≤ stT339o2 185 := by
  have hc : ((114139/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41958295373/625000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((114139/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c186 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((440241/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1234797/10000000) (δ := 8539/1000000000) (ψ := -65899/100000) 339 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t186 : ((8069544469/125000000000 : ℚ) : ℝ) ≤ stT339o2 186 := by
  have hc : ((55027/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8069544469/125000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((55027/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c187 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((167229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 701389/2000000) (δ := 4307/500000000) (ψ := -65899/100000) 339 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t187 : ((15281665211/1250000000000 : ℚ) : ℝ) ≤ stT339o2 187 := by
  have hc : ((167179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15281665211/1250000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((167179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c188 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-671311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5766931/10000000) (δ := 1083/125000000) (ψ := -65899/100000) 339 141
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t188 : ((-19585614453/400000000000 : ℚ) : ℝ) ≤ stT339o2 188 := by
  have hc : ((-671361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19585614453/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-671361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c189 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-997927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7692997/10000000) (δ := 1079/125000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t189 : ((-725921483961/10000000000000 : ℚ) : ℝ) ≤ stT339o2 189 := by
  have hc : ((-997977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-725921483961/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-997977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c190 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-114893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1364217/2500000) (δ := 2133/250000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t190 : ((-83359483731/2000000000000 : ℚ) : ℝ) ≤ stT339o2 190 := by
  have hc : ((-114903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83359483731/2000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-114903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c191 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((137131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -646487/2000000) (δ := 1079/125000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t191 : ((24801584211/1250000000000 : ℚ) : ℝ) ≤ stT339o2 191 := by
  have hc : ((68553/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24801584211/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((68553/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c192 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((917971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -509827/5000000) (δ := 8671/1000000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t192 : ((662451652727/10000000000000 : ℚ) : ℝ) ≤ stT339o2 192 := by
  have hc : ((917921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((662451652727/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((917921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c193 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((445181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 590821/5000000) (δ := 4241/500000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t193 : ((16021498307/250000000000 : ℚ) : ℝ) ≤ stT339o2 193 := by
  have hc : ((111289/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16021498307/250000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((111289/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c194 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((11017/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1685791/5000000) (δ := 4241/500000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t194 : ((7907948391/500000000000 : ℚ) : ℝ) ≤ stT339o2 194 := by
  have hc : ((22029/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7907948391/500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((22029/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c195 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-75579/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 22201/40000) (δ := 4291/500000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t195 : ((-43302185043/1000000000000 : ℚ) : ℝ) ≤ stT339o2 195 := by
  have hc : ((-302341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43302185043/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-302341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c196 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-249629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3858887/5000000) (δ := 8521/1000000000) (ψ := -65899/100000) 339 142
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t196 : ((-178315428469/2500000000000 : ℚ) : ℝ) ≤ stT339o2 196 := by
  have hc : ((-499283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-178315428469/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-499283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c197 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-690859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5833683/10000000) (δ := 4289/500000000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t197 : ((-492252626139/10000000000000 : ℚ) : ℝ) ≤ stT339o2 197 := by
  have hc : ((-690909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-492252626139/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-690909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c198 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((95407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -368811/1000000) (δ := 341/40000000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t198 : ((67767263833/10000000000000 : ℚ) : ℝ) ≤ stT339o2 198 := by
  have hc : ((95357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67767263833/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((95357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c199 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((813101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -776671/5000000) (δ := 533/62500000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t199 : ((576356405931/10000000000000 : ℚ) : ℝ) ≤ stT339o2 199 := by
  have hc : ((813051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((576356405931/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((813051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c200 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((974057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 114141/2000000) (δ := 4289/500000000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t200 : ((344363096871/5000000000000 : ℚ) : ℝ) ≤ stT339o2 200 := by
  have hc : ((974007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344363096871/5000000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((974007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c201 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((476893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 13421/50000) (δ := 343/40000000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t201 : ((67267765167/2000000000000 : ℚ) : ℝ) ≤ stT339o2 201 := by
  have hc : ((476843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67267765167/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((476843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c202 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-337313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 598393/1250000) (δ := 69/8000000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t202 : ((-118683966037/5000000000000 : ℚ) : ℝ) ≤ stT339o2 202 := by
  have hc : ((-337363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118683966037/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-337363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c203 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-462513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6879749/10000000) (δ := 4239/500000000) (ψ := -65899/100000) 339 143
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t203 : ((-162319154147/2500000000000 : ℚ) : ℝ) ≤ stT339o2 203 := by
  have hc : ((-231269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-162319154147/2500000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-231269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c204 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-903371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6745907/10000000) (δ := 1071/125000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t204 : ((-632522082361/10000000000000 : ℚ) : ℝ) ≤ stT339o2 204 := by
  have hc : ((-903421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-632522082361/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-903421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c205 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-294289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4673769/10000000) (δ := 1717/200000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t205 : ((-205575482109/10000000000000 : ℚ) : ℝ) ≤ stT339o2 205 := by
  have hc : ((-294339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205575482109/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-294339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c206 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((502173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2611717/10000000) (δ := 1697/200000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t206 : ((349845664159/10000000000000 : ℚ) : ℝ) ≤ stT339o2 206 := by
  have hc : ((502123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((349845664159/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((502123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c207 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((487523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -111933/2000000) (δ := 1717/200000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t207 : ((21177156869/312500000000 : ℚ) : ℝ) ≤ stT339o2 207 := by
  have hc : ((243749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21177156869/312500000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((243749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c208 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((165853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1482513/10000000) (δ := 4259/500000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t208 : ((919931121/16000000000 : ℚ) : ℝ) ≤ stT339o2 208 := by
  have hc : ((165843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((919931121/16000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((165843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c209 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((16409/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3514903/10000000) (δ := 1707/200000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t209 : ((1418359557/125000000000 : ℚ) : ℝ) ≤ stT339o2 209 := by
  have hc : ((4101/25000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1418359557/125000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((4101/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c210 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-60059/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5537589/10000000) (δ := 1717/200000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t210 : ((-647626941/15625000000 : ℚ) : ℝ) ≤ stT339o2 210 := by
  have hc : ((-1877/3125 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-647626941/15625000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-1877/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c211 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-124081/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1510131/2000000) (δ := 2167/250000000) (ψ := -65899/100000) 339 144
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t211 : ((-341701045721/5000000000000 : ℚ) : ℝ) ≤ stT339o2 211 := by
  have hc : ((-496349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341701045721/5000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-496349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c212 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-777521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -246151/400000) (δ := 8643/1000000000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t212 : ((-534038095513/10000000000000 : ℚ) : ℝ) ≤ stT339o2 212 := by
  have hc : ((-777571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-534038095513/10000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-777571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c213 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-92929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -83193/200000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t213 : ((-63708188031/10000000000000 : ℚ) : ℝ) ≤ stT339o2 213 := by
  have hc : ((-92979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63708188031/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-92979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c214 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((644873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -16991/78125) (δ := 861/100000000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t214 : ((88158266091/2000000000000 : ℚ) : ℝ) ≤ stT339o2 214 := by
  have hc : ((644823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88158266091/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((644823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c215 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((996823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7973/400000) (δ := 8543/1000000000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t215 : ((339896602681/5000000000000 : ℚ) : ℝ) ≤ stT339o2 215 := by
  have hc : ((996773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((339896602681/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((996773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c216 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((47527/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 441761/2500000) (δ := 861/100000000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t216 : ((258686898883/5000000000000 : ℚ) : ℝ) ≤ stT339o2 216 := by
  have hc : ((380191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258686898883/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((380191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c217 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((40493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3724303/10000000) (δ := 107/12500000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t217 : ((1716966187/312500000000 : ℚ) : ℝ) ≤ stT339o2 217 := by
  have hc : ((10117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1716966187/312500000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((10117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c218 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-642867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5672579/10000000) (δ := 8643/1000000000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t218 : ((-217719341631/5000000000000 : ℚ) : ℝ) ≤ stT339o2 218 := by
  have hc : ((-642917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217719341631/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-642917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c219 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-497659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1522391/2000000) (δ := 107/12500000) (ψ := -65899/100000) 339 145
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t219 : ((-42037998849/625000000000 : ℚ) : ℝ) ≤ stT339o2 219 := by
  have hc : ((-124421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42037998849/625000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-124421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c220 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-780459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -385343/625000) (δ := 8553/1000000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t220 : ((-2631095839/50000000000 : ℚ) : ℝ) ≤ stT339o2 220 := by
  have hc : ((-780509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2631095839/50000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-780509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c221 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-15793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4243697/10000000) (δ := 8553/1000000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t221 : ((-42510915581/5000000000000 : ℚ) : ℝ) ≤ stT339o2 221 := by
  have hc : ((-63197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42510915581/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-63197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c222 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((298013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -466127/2000000) (δ := 17/2000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t222 : ((12499777133/312500000000 : ℚ) : ℝ) ≤ stT339o2 222 := by
  have hc : ((74497/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12499777133/312500000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((74497/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c223 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((246377/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -426133/10000000) (δ := 17/2000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t223 : ((329955482121/5000000000000 : ℚ) : ℝ) ≤ stT339o2 223 := by
  have hc : ((492729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329955482121/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((492729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c224 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((166417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 367463/2500000) (δ := 173/20000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t224 : ((111185336271/2000000000000 : ℚ) : ℝ) ≤ stT339o2 224 := by
  have hc : ((166407/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111185336271/2000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((166407/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c225 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((225869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 839351/2500000) (δ := 173/20000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t225 : ((75272924727/5000000000000 : ℚ) : ℝ) ≤ stT339o2 225 := by
  have hc : ((225819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75272924727/5000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((225819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c226 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-500193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 81821/156250) (δ := 17003/1000000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t226 : ((-332757141413/10000000000000 : ℚ) : ℝ) ≤ stT339o2 226 := by
  have hc : ((-500243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332757141413/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-500243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c227 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-477871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3553711/5000000) (δ := 173/20000000) (ψ := -65899/100000) 339 146
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t227 : ((-9912220147/156250000000 : ℚ) : ℝ) ≤ stT339o2 227 := by
  have hc : ((-59737/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9912220147/156250000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-59737/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c228 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-450997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3368953/5000000) (δ := 8557/1000000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t228 : ((-149348493437/2500000000000 : ℚ) : ℝ) ≤ stT339o2 228 := by
  have hc : ((-225511/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149348493437/2500000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-225511/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c229 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-373303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4883407/10000000) (δ := 2149/250000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t229 : ((-246718756107/10000000000000 : ℚ) : ℝ) ≤ stT339o2 229 := by
  have hc : ((-373353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246718756107/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-373353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c230 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((87131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3037001/10000000) (δ := 4273/500000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t230 : ((5744419653/250000000000 : ℚ) : ℝ) ≤ stT339o2 230 := by
  have hc : ((174237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5744419653/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((174237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c231 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((887253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -299651/2500000) (δ := 4273/500000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t231 : ((583736101053/10000000000000 : ℚ) : ℝ) ≤ stT339o2 231 := by
  have hc : ((887203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583736101053/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((887203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c232 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((968233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 631827/10000000) (δ := 8607/1000000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t232 : ((158910780339/2500000000000 : ℚ) : ℝ) ≤ stT339o2 232 := by
  have hc : ((968183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158910780339/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((968183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c233 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((277777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1227209/5000000) (δ := 8557/1000000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t233 : ((22745145999/625000000000 : ℚ) : ℝ) ≤ stT339o2 233 := by
  have hc : ((34719/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22745145999/625000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((34719/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c234 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-136461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1067303/2500000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t234 : ((-89240107431/10000000000000 : ℚ) : ℝ) ≤ stT339o2 234 := by
  have hc : ((-136511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89240107431/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-136511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c235 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-757649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6076251/10000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 147
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t235 : ((-494269030971/10000000000000 : ℚ) : ℝ) ≤ stT339o2 235 := by
  have hc : ((-757699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-494269030971/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-757699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c236 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-999963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3916171/5000000) (δ := 2141/250000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t236 : ((-130190692457/2000000000000 : ℚ) : ℝ) ≤ stT339o2 236 := by
  have hc : ((-1000013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130190692457/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-1000013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c237 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-374133/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -30203/50000) (δ := 4257/500000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t237 : ((-12152090603/250000000000 : ℚ) : ℝ) ≤ stT339o2 237 := by
  have hc : ((-187079/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12152090603/250000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-187079/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c238 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-131383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4256401/10000000) (δ := 8589/1000000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t238 : ((-21298849083/2500000000000 : ℚ) : ℝ) ≤ stT339o2 238 := by
  have hc : ((-131433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21298849083/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-131433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c239 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((547131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2479659/10000000) (δ := 4307/500000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t239 : ((176938578263/5000000000000 : ℚ) : ℝ) ≤ stT339o2 239 := by
  have hc : ((547081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((176938578263/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((547081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c240 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((191981/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -355167/5000000) (δ := 8639/1000000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t240 : ((123916704587/2000000000000 : ℚ) : ℝ) ≤ stT339o2 240 := by
  have hc : ((191971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123916704587/2000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((191971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c241 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((36513/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1051619/10000000) (δ := 4257/500000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t241 : ((5879694929/100000000000 : ℚ) : ℝ) ≤ stT339o2 241 := by
  have hc : ((36511/40000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5879694929/100000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((36511/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c242 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((433419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2806283/10000000) (δ := 4257/500000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t242 : ((34822499257/1250000000000 : ℚ) : ℝ) ≤ stT339o2 242 := by
  have hc : ((433369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34822499257/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((433369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c243 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-248067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4553701/10000000) (δ := 2141/250000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t243 : ((-159167303617/10000000000000 : ℚ) : ℝ) ≤ stT339o2 243 := by
  have hc : ((-248117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159167303617/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-248117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c244 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-405771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6293957/10000000) (δ := 8589/1000000000) (ψ := -65899/100000) 339 148
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t244 : ((-12989225613/250000000000 : ℚ) : ℝ) ≤ stT339o2 244 := by
  have hc : ((-101449/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12989225613/250000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-101449/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c245 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-249401/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -768089/1000000) (δ := 8541/500000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t245 : ((-318689097279/5000000000000 : ℚ) : ℝ) ≤ stT339o2 245 := by
  have hc : ((-498827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318689097279/5000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-498827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c246 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-90633/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -744351/1250000) (δ := 1079/125000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t246 : ((-231158004389/5000000000000 : ℚ) : ℝ) ≤ stT339o2 246 := by
  have hc : ((-362557/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-231158004389/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-362557/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c247 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-61593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4235739/10000000) (δ := 1079/125000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t247 : ((-3920660913/500000000000 : ℚ) : ℝ) ≤ stT339o2 247 := by
  have hc : ((-30809/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3920660913/500000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-30809/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c248 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((66541/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2523619/10000000) (δ := 8521/1000000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t248 : ((33799653/1000000000 : ℚ) : ℝ) ≤ stT339o2 248 := by
  have hc : ((266139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33799653/1000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((266139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c249 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((473447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -818407/10000000) (δ := 4291/500000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t249 : ((37502360441/625000000000 : ℚ) : ℝ) ≤ stT339o2 249 := by
  have hc : ((236711/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37502360441/625000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((236711/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c250 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((938681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 440013/5000000) (δ := 8621/1000000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t250 : ((118728373821/2000000000000 : ℚ) : ℝ) ≤ stT339o2 250 := by
  have hc : ((938631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118728373821/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((938631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c251 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((128993/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55254529/20000000 : ℚ) : ℝ) ≤ Real.log ((251 : ℕ)) / 2 := by
    have h := (log_br_251).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((251 : ℕ)) / 2 ≤ ((5525453/2000000 : ℚ) : ℝ) := by
    have h := (log_br_251).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 642909/2500000) (δ := 8621/1000000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t251 : ((81411717717/2500000000000 : ℚ) : ℝ) ≤ stT339o2 251 := by
  have hc : ((257961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((251 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81411717717/2500000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((257961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c252 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-65713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5529429/2000000 : ℚ) : ℝ) ≤ Real.log ((252 : ℕ)) / 2 := by
    have h := (log_br_252).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((252 : ℕ)) / 2 ≤ ((55294291/20000000 : ℚ) : ℝ) := by
    have h := (log_br_252).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1064127/2500000) (δ := 4241/500000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t252 : ((-20705530729/2500000000000 : ℚ) : ℝ) ≤ stT339o2 252 := by
  have hc : ((-32869/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((252 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20705530729/2500000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-32869/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c253 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-719509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27666947/10000000 : ℚ) : ℝ) ≤ Real.log ((253 : ℕ)) / 2 := by
    have h := (log_br_253).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((253 : ℕ)) / 2 ≤ ((11066779/4000000 : ℚ) : ℝ) := by
    have h := (log_br_253).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 741841/1250000) (δ := 8671/1000000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t253 : ((-90476629101/2000000000000 : ℚ) : ℝ) ≤ stT339o2 253 := by
  have hc : ((-719559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((253 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90476629101/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-719559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c254 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-497549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27686671/10000000 : ℚ) : ℝ) ≤ Real.log ((254 : ℕ)) / 2 := by
    have h := (log_br_254).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((254 : ℕ)) / 2 ≤ ((55373343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_254).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7606337/10000000) (δ := 8671/1000000000) (ψ := -65899/100000) 339 149
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t254 : ((-609776937/9765625000 : ℚ) : ℝ) ≤ stT339o2 254 := by
  have hc : ((-248787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((254 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-609776937/9765625000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-248787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c255 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-843539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11082527/4000000 : ℚ) : ℝ) ≤ Real.log ((255 : ℕ)) / 2 := by
    have h := (log_br_255).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((255 : ℕ)) / 2 ≤ ((13853159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_255).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3218293/5000000) (δ := 341/40000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t255 : ((-21131060861/400000000000 : ℚ) : ℝ) ≤ stT339o2 255 := by
  have hc : ((-843589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((255 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21131060861/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-843589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c256 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-166947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/10000000 : ℚ) : ℝ) ≤ Real.log ((256 : ℕ)) / 2 := by
    have h := (log_br_256).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((256 : ℕ)) / 2 ≤ ((2218071/800000 : ℚ) : ℝ) := by
    have h := (log_br_256).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4778071/10000000) (δ := 343/40000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t256 : ((-26089416743/1250000000000 : ℚ) : ℝ) ≤ stT339o2 256 := by
  have hc : ((-41743/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((256 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).2
  have h0 : (0:ℝ) ≤ ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26089416743/1250000000000 : ℚ) : ℝ)
      = ((625001/10000000 : ℚ) : ℝ) * ((-41743/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c257 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((19683/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1387269/500000 : ℚ) : ℝ) ≤ Real.log ((257 : ℕ)) / 2 := by
    have h := (log_br_257).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((257 : ℕ)) / 2 ≤ ((55490761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_257).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3126039/10000000) (δ := 4239/500000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t257 : ((49103807149/2500000000000 : ℚ) : ℝ) ≤ stT339o2 257 := by
  have hc : ((157439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((257 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49103807149/2500000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((157439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c258 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((103717/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11105919/4000000 : ℚ) : ℝ) ≤ Real.log ((258 : ℕ)) / 2 := by
    have h := (log_br_258).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((258 : ℕ)) / 2 ≤ ((13882399/5000000 : ℚ) : ℝ) := by
    have h := (log_br_258).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -740203/5000000) (δ := 341/40000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t258 : ((64567409049/1250000000000 : ℚ) : ℝ) ≤ stT339o2 258 := by
  have hc : ((414843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((258 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64567409049/1250000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((414843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c259 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((997981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1389207/500000 : ℚ) : ℝ) ≤ Real.log ((259 : ℕ)) / 2 := by
    have h := (log_br_259).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((259 : ℕ)) / 2 ≤ ((55568281/20000000 : ℚ) : ℝ) := by
    have h := (log_br_259).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 158871/10000000) (δ := 4239/500000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t259 : ((620083387539/10000000000000 : ℚ) : ℝ) ≤ stT339o2 259 := by
  have hc : ((997931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((259 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).1
  have hw2 : ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((621369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((620083387539/10000000000000 : ℚ) : ℝ)
      = ((621369/10000000 : ℚ) : ℝ) * ((997931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c260 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((188489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1737713/625000 : ℚ) : ℝ) ≤ Real.log ((260 : ℕ)) / 2 := by
    have h := (log_br_260).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((260 : ℕ)) / 2 ≤ ((55606817/20000000 : ℚ) : ℝ) := by
    have h := (log_br_260).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 895917/5000000) (δ := 4239/500000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t260 : ((233776072869/5000000000000 : ℚ) : ℝ) ≤ stT339o2 260 := by
  have hc : ((376953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((260 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233776072869/5000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((376953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c261 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((201987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13911301/5000000 : ℚ) : ℝ) ≤ Real.log ((261 : ℕ)) / 2 := by
    have h := (log_br_261).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((261 : ℕ)) / 2 ≤ ((11129041/4000000 : ℚ) : ℝ) := by
    have h := (log_br_261).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 136741/400000) (δ := 347/40000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t261 : ((15624471501/1250000000000 : ℚ) : ℝ) ≤ stT339o2 261 := by
  have hc : ((201937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((261 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15624471501/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((201937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c262 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-107569/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13920861/5000000 : ℚ) : ℝ) ≤ Real.log ((262 : ℕ)) / 2 := by
    have h := (log_br_262).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((262 : ℕ)) / 2 ≤ ((55683447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_262).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1259747/2500000) (δ := 12739/500000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t262 : ((-132928346889/5000000000000 : ℚ) : ℝ) ≤ stT339o2 262 := by
  have hc : ((-215163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((262 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132928346889/5000000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-215163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c263 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-443431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2786077/1000000 : ℚ) : ℝ) ≤ Real.log ((263 : ℕ)) / 2 := by
    have h := (log_br_263).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((263 : ℕ)) / 2 ≤ ((55721541/20000000 : ℚ) : ℝ) := by
    have h := (log_br_263).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6653263/10000000) (δ := 347/40000000) (ψ := -65899/100000) 339 150
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t263 : ((-4272608483/78125000000 : ℚ) : ℝ) ≤ stT339o2 263 := by
  have hc : ((-13858/15625 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((263 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4272608483/78125000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-13858/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c264 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-246687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5575949/2000000 : ℚ) : ℝ) ≤ Real.log ((264 : ℕ)) / 2 := by
    have h := (log_br_264).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((264 : ℕ)) / 2 ≤ ((55759493/20000000 : ℚ) : ℝ) := by
    have h := (log_br_264).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3723263/5000000) (δ := 12743/500000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t264 : ((-151833180871/2500000000000 : ℚ) : ℝ) ≤ stT339o2 264 := by
  have hc : ((-493399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((264 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151833180871/2500000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-493399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c265 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-43373/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27898649/10000000 : ℚ) : ℝ) ≤ Real.log ((265 : ℕ)) / 2 := by
    have h := (log_br_265).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((265 : ℕ)) / 2 ≤ ((55797299/20000000 : ℚ) : ℝ) := by
    have h := (log_br_265).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1168891/2000000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t265 : ((-26645780083/625000000000 : ℚ) : ℝ) ≤ stT339o2 265 := by
  have hc : ((-347009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((265 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26645780083/625000000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-347009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c266 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-12821/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55834963/20000000 : ℚ) : ℝ) ≤ Real.log ((266 : ℕ)) / 2 := by
    have h := (log_br_266).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((266 : ℕ)) / 2 ≤ ((13958741/5000000 : ℚ) : ℝ) := by
    have h := (log_br_266).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -10621/25000) (δ := 1067/125000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t266 : ((-196603341/25000000000 : ℚ) : ℝ) ≤ stT339o2 266 := by
  have hc : ((-6413/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((266 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196603341/25000000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-6413/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c267 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((485951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27936243/10000000 : ℚ) : ℝ) ≤ Real.log ((267 : ℕ)) / 2 := by
    have h := (log_br_267).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((267 : ℕ)) / 2 ≤ ((55872487/20000000 : ℚ) : ℝ) := by
    have h := (log_br_267).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2658363/10000000) (δ := 4243/500000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t267 : ((29736655299/1000000000000 : ℚ) : ℝ) ≤ stT339o2 267 := by
  have hc : ((485901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((267 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29736655299/1000000000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((485901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c268 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((909089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55909869/20000000 : ℚ) : ℝ) ≤ Real.log ((268 : ℕ)) / 2 := by
    have h := (log_br_268).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((268 : ℕ)) / 2 ≤ ((5590987/2000000 : ℚ) : ℝ) := by
    have h := (log_br_268).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -537129/5000000) (δ := 2159/250000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t268 : ((555283746033/10000000000000 : ℚ) : ℝ) ≤ stT339o2 268 := by
  have hc : ((909039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((268 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((555283746033/10000000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((909039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c269 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((979751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55947113/20000000 : ℚ) : ℝ) ≤ Real.log ((269 : ℕ)) / 2 := by
    have h := (log_br_269).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((269 : ℕ)) / 2 ≤ ((27973557/10000000 : ℚ) : ℝ) := by
    have h := (log_br_269).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 125989/2500000) (δ := 8517/1000000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t269 : ((59733349671/1000000000000 : ℚ) : ℝ) ≤ stT339o2 269 := by
  have hc : ((979701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((269 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59733349671/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((979701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c270 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((134897/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55984219/20000000 : ℚ) : ℝ) ≤ Real.log ((270 : ℕ)) / 2 := by
    have h := (log_br_270).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((270 : ℕ)) / 2 ≤ ((2799211/1000000 : ℚ) : ℝ) := by
    have h := (log_br_270).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2076323/10000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t270 : ((4104476523/100000000000 : ℚ) : ℝ) ≤ stT339o2 270 := by
  have hc : ((134887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((270 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4104476523/100000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((134887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c271 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((56699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14005297/5000000 : ℚ) : ℝ) ≤ Real.log ((271 : ℕ)) / 2 := by
    have h := (log_br_271).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((271 : ℕ)) / 2 ≤ ((56021189/20000000 : ℚ) : ℝ) := by
    have h := (log_br_271).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 910721/2500000) (δ := 8567/1000000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t271 : ((537921271/78125000000 : ℚ) : ℝ) ≤ stT339o2 271 := by
  have hc : ((28337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((271 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((537921271/78125000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((28337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c272 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-488753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2802901/1000000 : ℚ) : ℝ) ≤ Real.log ((272 : ℕ)) / 2 := by
    have h := (log_br_272).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((272 : ℕ)) / 2 ≤ ((56058021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_272).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 130091/250000) (δ := 8567/1000000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t272 : ((-14819040551/500000000000 : ℚ) : ℝ) ≤ stT339o2 272 := by
  have hc : ((-488803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((272 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14819040551/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-488803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c273 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-18111/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56094717/20000000 : ℚ) : ℝ) ≤ Real.log ((273 : ℕ)) / 2 := by
    have h := (log_br_273).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((273 : ℕ)) / 2 ≤ ((28047359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_273).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1689669/2500000) (δ := 2159/250000000) (ψ := -65899/100000) 339 151
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t273 : ((-42819881/781250000 : ℚ) : ℝ) ≤ stT339o2 273 := by
  have hc : ((-566/625 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((273 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42819881/781250000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-566/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c274 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-983549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56131281/20000000 : ℚ) : ℝ) ≤ Real.log ((274 : ℕ)) / 2 := by
    have h := (log_br_274).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((274 : ℕ)) / 2 ≤ ((28065641/10000000 : ℚ) : ℝ) := by
    have h := (log_br_274).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -462493/625000) (δ := 8543/1000000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t274 : ((-594214778677/10000000000000 : ℚ) : ℝ) ≤ stT339o2 274 := by
  have hc : ((-983599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((274 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-594214778677/10000000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-983599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c275 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-348673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5616771/2000000 : ℚ) : ℝ) ≤ Real.log ((275 : ℕ)) / 2 := by
    have h := (log_br_275).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((275 : ℕ)) / 2 ≤ ((56167711/20000000 : ℚ) : ℝ) := by
    have h := (log_br_275).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5856209/10000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t275 : ((-105136457027/2500000000000 : ℚ) : ℝ) ≤ stT339o2 275 := by
  have hc : ((-174349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((275 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105136457027/2500000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-174349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c276 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-155799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7025501/2500000 : ℚ) : ℝ) ≤ Real.log ((276 : ℕ)) / 2 := by
    have h := (log_br_276).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((276 : ℕ)) / 2 ≤ ((56204009/20000000 : ℚ) : ℝ) := by
    have h := (log_br_276).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2159041/5000000) (δ := 433/50000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t276 : ((-9381018857/1000000000000 : ℚ) : ℝ) ≤ stT339o2 276 := by
  have hc : ((-155849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((276 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9381018857/1000000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-155849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c277 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((220447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2249607/800000 : ℚ) : ℝ) ≤ Real.log ((277 : ℕ)) / 2 := by
    have h := (log_br_277).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((277 : ℕ)) / 2 ≤ ((3515011/1250000 : ℚ) : ℝ) := by
    have h := (log_br_277).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -557101/2000000) (δ := 851/100000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t277 : ((66219287451/2500000000000 : ℚ) : ℝ) ≤ stT339o2 277 := by
  have hc : ((110211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((277 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66219287451/2500000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((110211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c278 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((875951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56276211/20000000 : ℚ) : ℝ) ≤ Real.log ((278 : ℕ)) / 2 := by
    have h := (log_br_278).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((278 : ℕ)) / 2 ≤ ((14069053/5000000 : ℚ) : ℝ) := by
    have h := (log_br_278).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1258479/10000000) (δ := 8643/1000000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t278 : ((6566629797/125000000000 : ℚ) : ℝ) ≤ stT339o2 278 := by
  have hc : ((875901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((278 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6566629797/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((875901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c279 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((99447/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56312117/20000000 : ℚ) : ℝ) ≤ Real.log ((279 : ℕ)) / 2 := by
    have h := (log_br_279).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((279 : ℕ)) / 2 ≤ ((28156059/10000000 : ℚ) : ℝ) := by
    have h := (log_br_279).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 263037/10000000) (δ := 861/100000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t279 : ((7441791791/125000000000 : ℚ) : ℝ) ≤ stT339o2 279 := by
  have hc : ((49721/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((279 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7441791791/125000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((49721/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c280 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((757273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7043487/2500000 : ℚ) : ℝ) ≤ Real.log ((280 : ℕ)) / 2 := by
    have h := (log_br_280).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((280 : ℕ)) / 2 ≤ ((56347897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_280).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 444793/2500000) (δ := 433/50000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t280 : ((226263532961/5000000000000 : ℚ) : ℝ) ≤ stT339o2 280 := by
  have hc : ((757223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((280 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226263532961/5000000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((757223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c281 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((25211/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28191773/10000000 : ℚ) : ℝ) ≤ Real.log ((281 : ℕ)) / 2 := by
    have h := (log_br_281).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((281 : ℕ)) / 2 ≤ ((56383547/20000000 : ℚ) : ℝ) := by
    have h := (log_br_281).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3289841/10000000) (δ := 107/12500000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t281 : ((7518307047/500000000000 : ℚ) : ℝ) ≤ stT339o2 281 := by
  have hc : ((12603/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((281 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7518307047/500000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((12603/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c282 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-170167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5641907/2000000 : ℚ) : ℝ) ≤ Real.log ((282 : ℕ)) / 2 := by
    have h := (log_br_282).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((282 : ℕ)) / 2 ≤ ((56419071/20000000 : ℚ) : ℝ) := by
    have h := (log_br_282).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4795171/10000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t282 : ((-1583562101/78125000000 : ℚ) : ℝ) ≤ stT339o2 282 := by
  have hc : ((-10637/31250 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((282 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).2
  have h0 : (0:ℝ) ≤ ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1583562101/78125000000 : ℚ) : ℝ)
      = ((148873/2500000 : ℚ) : ℝ) * ((-10637/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c283 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-811823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14113617/5000000 : ℚ) : ℝ) ≤ Real.log ((283 : ℕ)) / 2 := by
    have h := (log_br_283).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((283 : ℕ)) / 2 ≤ ((56454469/20000000 : ℚ) : ℝ) := by
    have h := (log_br_283).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6295161/10000000) (δ := 8493/1000000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t283 : ((-482608974247/10000000000000 : ℚ) : ℝ) ≤ stT339o2 283 := by
  have hc : ((-811873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((283 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-482608974247/10000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-811873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c284 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-999671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28244871/10000000 : ℚ) : ℝ) ≤ Real.log ((284 : ℕ)) / 2 := by
    have h := (log_br_284).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((284 : ℕ)) / 2 ≤ ((56489743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_284).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7789897/10000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 152
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t284 : ((-593225443911/10000000000000 : ℚ) : ℝ) ≤ stT339o2 284 := by
  have hc : ((-999721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((284 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-593225443911/10000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-999721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c285 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-33673/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56524891/20000000 : ℚ) : ℝ) ≤ Real.log ((285 : ℕ)) / 2 := by
    have h := (log_br_285).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((285 : ℕ)) / 2 ≤ ((14131223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_285).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1607157/2500000) (δ := 8603/1000000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t285 : ((-797894103/16000000000 : ℚ) : ℝ) ≤ stT339o2 285 := by
  have hc : ((-1347/1600 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((285 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-797894103/16000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-1347/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c286 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-12369/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28279959/10000000 : ℚ) : ℝ) ≤ Real.log ((286 : ℕ)) / 2 := by
    have h := (log_br_286).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((286 : ℕ)) / 2 ≤ ((56559919/20000000 : ℚ) : ℝ) := by
    have h := (log_br_286).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4944359/10000000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t286 : ((-117037990777/5000000000000 : ℚ) : ℝ) ≤ stT339o2 286 := by
  have hc : ((-197929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((286 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117037990777/5000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-197929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c287 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((45907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28297411/10000000 : ℚ) : ℝ) ≤ Real.log ((287 : ℕ)) / 2 := by
    have h := (log_br_287).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((287 : ℕ)) / 2 ≤ ((56594823/20000000 : ℚ) : ℝ) := by
    have h := (log_br_287).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1732651/5000000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t287 : ((54181302709/5000000000000 : ℚ) : ℝ) ≤ stT339o2 287 := by
  have hc : ((91789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((287 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54181302709/5000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((91789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c288 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((349583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14157401/5000000 : ℚ) : ℝ) ≤ Real.log ((288 : ℕ)) / 2 := by
    have h := (log_br_288).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((288 : ℕ)) / 2 ≤ ((11325921/4000000 : ℚ) : ℝ) := by
    have h := (log_br_288).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -995707/5000000) (δ := 43/5000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t288 : ((20597879929/500000000000 : ℚ) : ℝ) ≤ stT339o2 288 := by
  have hc : ((174779/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((288 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20597879929/500000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((174779/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c289 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((97823/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/10000000 : ℚ) : ℝ) ≤ Real.log ((289 : ℕ)) / 2 := by
    have h := (log_br_289).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((289 : ℕ)) / 2 ≤ ((56664267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_289).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -130653/2500000) (δ := 17/2000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t289 : ((5753997123/100000000000 : ℚ) : ℝ) ≤ stT339o2 289 := by
  have hc : ((48909/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((289 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5753997123/100000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((48909/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c290 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((232493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56698809/20000000 : ℚ) : ℝ) ≤ Real.log ((290 : ℕ)) / 2 := by
    have h := (log_br_290).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((290 : ℕ)) / 2 ≤ ((5669881/2000000 : ℚ) : ℝ) := by
    have h := (log_br_290).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 235287/2500000) (δ := 173/20000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t290 : ((13651719921/250000000000 : ℚ) : ℝ) ≤ stT339o2 290 := by
  have hc : ((464961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((290 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13651719921/250000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((464961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c291 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((286789/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3545827/1250000 : ℚ) : ℝ) ≤ Real.log ((291 : ℕ)) / 2 := by
    have h := (log_br_291).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((291 : ℕ)) / 2 ≤ ((56733233/20000000 : ℚ) : ℝ) := by
    have h := (log_br_291).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1199911/5000000) (δ := 8553/1000000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t291 : ((4202598111/125000000000 : ℚ) : ℝ) ≤ stT339o2 291 := by
  have hc : ((71691/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((291 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4202598111/125000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((71691/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c292 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((459/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28383769/10000000 : ℚ) : ℝ) ≤ Real.log ((292 : ℕ)) / 2 := by
    have h := (log_br_292).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((292 : ℕ)) / 2 ≤ ((56767539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_292).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3853539/10000000) (δ := 17/2000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t292 : ((1716172183/1000000000000 : ℚ) : ℝ) ≤ stT339o2 292 := by
  have hc : ((14663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((292 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1716172183/1000000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((14663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c293 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-522777/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28400863/10000000 : ℚ) : ℝ) ≤ Real.log ((293 : ℕ)) / 2 := by
    have h := (log_br_293).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((293 : ℕ)) / 2 ≤ ((56801727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_293).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1060451/2000000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t293 : ((-305439193189/10000000000000 : ℚ) : ℝ) ≤ stT339o2 293 := by
  have hc : ((-522827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((293 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305439193189/10000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-522827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c294 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-90339/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56835797/20000000 : ℚ) : ℝ) ≤ Real.log ((294 : ℕ)) / 2 := by
    have h := (log_br_294).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((294 : ℕ)) / 2 ≤ ((28417899/10000000 : ℚ) : ℝ) := by
    have h := (log_br_294).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3373007/5000000) (δ := 8503/1000000000) (ψ := -65899/100000) 339 153
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t294 : ((-1646553279/31250000000 : ℚ) : ℝ) ≤ stT339o2 294 := by
  have hc : ((-11293/12500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((294 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1646553279/31250000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-11293/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c295 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-247813/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56869753/20000000 : ℚ) : ℝ) ≤ Real.log ((295 : ℕ)) / 2 := by
    have h := (log_br_295).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((295 : ℕ)) / 2 ≤ ((28434877/10000000 : ℚ) : ℝ) := by
    have h := (log_br_295).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -940383/1250000) (δ := 2149/250000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t295 : ((-288579412173/5000000000000 : ℚ) : ℝ) ≤ stT339o2 295 := by
  have hc : ((-495651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((295 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-288579412173/5000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-495651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c296 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-760981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28451797/10000000 : ℚ) : ℝ) ≤ Real.log ((296 : ℕ)) / 2 := by
    have h := (log_br_296).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((296 : ℕ)) / 2 ≤ ((11380719/4000000 : ℚ) : ℝ) := by
    have h := (log_br_296).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6089051/10000000) (δ := 8607/1000000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t296 : ((-442340897409/10000000000000 : ℚ) : ℝ) ≤ stT339o2 296 := by
  have hc : ((-761031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((296 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-442340897409/10000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-761031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c297 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-288971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((56937321/20000000 : ℚ) : ℝ) ≤ Real.log ((297 : ℕ)) / 2 := by
    have h := (log_br_297).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((297 : ℕ)) / 2 ≤ ((28468661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_297).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -465987/1000000) (δ := 2149/250000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t297 : ((-167707036439/10000000000000 : ℚ) : ℝ) ≤ stT339o2 297 := by
  have hc : ((-289021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((297 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167707036439/10000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-289021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c298 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((68269/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28485467/10000000 : ℚ) : ℝ) ≤ Real.log ((298 : ℕ)) / 2 := by
    have h := (log_br_298).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((298 : ℕ)) / 2 ≤ ((11394187/4000000 : ℚ) : ℝ) := by
    have h := (log_br_298).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3235519/10000000) (δ := 4273/500000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t298 : ((19769949173/1250000000000 : ℚ) : ℝ) ≤ stT339o2 298 := by
  have hc : ((136513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((298 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19769949173/1250000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((136513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c299 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((747593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11400887/4000000 : ℚ) : ℝ) ≤ Real.log ((299 : ℕ)) / 2 := by
    have h := (log_br_299).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((299 : ℕ)) / 2 ≤ ((14251109/5000000 : ℚ) : ℝ) := by
    have h := (log_br_299).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -907957/5000000) (δ := 531/62500000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t299 : ((216157291251/5000000000000 : ℚ) : ℝ) ≤ stT339o2 299 := by
  have hc : ((747543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((299 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((216157291251/5000000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((747543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c300 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((24679/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((222804/78125 : ℚ) : ℝ) ≤ Real.log ((300 : ℕ)) / 2 := by
    have h := (log_br_300).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((300 : ℕ)) / 2 ≤ ((2281513/800000 : ℚ) : ℝ) := by
    have h := (log_br_300).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -80211/2000000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t300 : ((1139815917/20000000000 : ℚ) : ℝ) ≤ stT339o2 300 := by
  have hc : ((98711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((300 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1139815917/20000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((98711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c301 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((919637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28535551/10000000 : ℚ) : ℝ) ≤ Real.log ((301 : ℕ)) / 2 := by
    have h := (log_br_301).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((301 : ℕ)) / 2 ≤ ((57071103/20000000 : ℚ) : ℝ) := by
    have h := (log_br_301).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 10091/100000) (δ := 4273/500000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t301 : ((53004075093/1000000000000 : ℚ) : ℝ) ≤ stT339o2 301 := by
  have hc : ((919587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((301 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53004075093/1000000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((919587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c302 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((71091/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5710427/2000000 : ℚ) : ℝ) ≤ Real.log ((302 : ℕ)) / 2 := by
    have h := (log_br_302).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((302 : ℕ)) / 2 ≤ ((57104271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_302).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1207297/5000000) (δ := 4273/500000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t302 : ((32723722493/1000000000000 : ℚ) : ℝ) ≤ stT339o2 302 := by
  have hc : ((284339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((302 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).1
  have hw2 : ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((115087/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32723722493/1000000000000 : ℚ) : ℝ)
      = ((115087/2000000 : ℚ) : ℝ) * ((284339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c303 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((44611/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3571083/1250000 : ℚ) : ℝ) ≤ Real.log ((303 : ℕ)) / 2 := by
    have h := (log_br_303).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((303 : ℕ)) / 2 ≤ ((57137329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_303).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3815427/10000000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t303 : ((6399895381/2500000000000 : ℚ) : ℝ) ≤ stT339o2 303 := by
  have hc : ((44561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((303 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).1
  have hw2 : ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143621/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6399895381/2500000000000 : ℚ) : ℝ)
      = ((143621/2500000 : ℚ) : ℝ) * ((44561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c304 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-245771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57170277/20000000 : ℚ) : ℝ) ≤ Real.log ((304 : ℕ)) / 2 := by
    have h := (log_br_304).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((304 : ℕ)) / 2 ≤ ((28585139/10000000 : ℚ) : ℝ) := by
    have h := (log_br_304).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5211641/10000000) (δ := 8557/1000000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t304 : ((-1762172973/62500000000 : ℚ) : ℝ) ≤ stT339o2 304 := by
  have hc : ((-61449/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((304 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1762172973/62500000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-61449/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c305 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-2742/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57203117/20000000 : ℚ) : ℝ) ≤ Real.log ((305 : ℕ)) / 2 := by
    have h := (log_br_305).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((305 : ℕ)) / 2 ≤ ((28601559/10000000 : ℚ) : ℝ) := by
    have h := (log_br_305).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1650809/2500000) (δ := 8557/1000000000) (ψ := -65899/100000) 339 154
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t305 : ((-50244989651/1000000000000 : ℚ) : ℝ) ≤ stT339o2 305 := by
  have hc : ((-87749/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((305 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50244989651/1000000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-87749/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c306 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-998513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57235851/20000000 : ℚ) : ℝ) ≤ Real.log ((306 : ℕ)) / 2 := by
    have h := (log_br_306).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((306 : ℕ)) / 2 ≤ ((14308963/5000000 : ℚ) : ℝ) := by
    have h := (log_br_306).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -964703/1250000) (δ := 2141/250000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t306 : ((-285420260853/5000000000000 : ℚ) : ℝ) ≤ stT339o2 306 := by
  have hc : ((-998563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((306 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).2
  have h0 : (0:ℝ) ≤ ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285420260853/5000000000000 : ℚ) : ℝ)
      = ((285831/5000000 : ℚ) : ℝ) * ((-998563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c307 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-821047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57268477/20000000 : ℚ) : ℝ) ≤ Real.log ((307 : ℕ)) / 2 := by
    have h := (log_br_307).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((307 : ℕ)) / 2 ≤ ((28634239/10000000 : ℚ) : ℝ) := by
    have h := (log_br_307).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6335097/10000000) (δ := 1083/125000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t307 : ((-468625511907/10000000000000 : ℚ) : ℝ) ≤ stT339o2 307 := by
  have hc : ((-821097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((307 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468625511907/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-821097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c308 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-400469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57300997/20000000 : ℚ) : ℝ) ≤ Real.log ((308 : ℕ)) / 2 := by
    have h := (log_br_308).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((308 : ℕ)) / 2 ≤ ((28650499/10000000 : ℚ) : ℝ) := by
    have h := (log_br_308).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2478531/5000000) (δ := 1083/125000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t308 : ((-228216927757/10000000000000 : ℚ) : ℝ) ≤ stT339o2 308 := by
  have hc : ((-400519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((308 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228216927757/10000000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-400519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c309 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((68487/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14333353/5000000 : ℚ) : ℝ) ≤ Real.log ((309 : ℕ)) / 2 := by
    have h := (log_br_309).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((309 : ℕ)) / 2 ≤ ((57333413/20000000 : ℚ) : ℝ) := by
    have h := (log_br_309).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3583477/10000000) (δ := 8539/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t309 : ((243416641/31250000000 : ℚ) : ℝ) ≤ stT339o2 309 := by
  have hc : ((34231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((309 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243416641/31250000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((34231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c310 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((632719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28682861/10000000 : ℚ) : ℝ) ≤ Real.log ((310 : ℕ)) / 2 := by
    have h := (log_br_310).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((310 : ℕ)) / 2 ≤ ((57365723/20000000 : ℚ) : ℝ) := by
    have h := (log_br_310).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2214341/10000000) (δ := 8639/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t310 : ((359331317909/10000000000000 : ℚ) : ℝ) ≤ stT339o2 310 := by
  have hc : ((632669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((310 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359331317909/10000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((632669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c311 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((235703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57397929/20000000 : ℚ) : ℝ) ≤ Real.log ((311 : ℕ)) / 2 := by
    have h := (log_br_311).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((311 : ℕ)) / 2 ≤ ((5739793/2000000 : ℚ) : ℝ) := by
    have h := (log_br_311).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -849569/10000000) (δ := 8489/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t311 : ((267295181907/5000000000000 : ℚ) : ℝ) ≤ stT339o2 311 := by
  have hc : ((471381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((311 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267295181907/5000000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((471381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c312 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((979203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57430031/20000000 : ℚ) : ℝ) ≤ Real.log ((312 : ℕ)) / 2 := by
    have h := (log_br_312).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((312 : ℕ)) / 2 ≤ ((3589377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_312).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 510753/10000000) (δ := 8589/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t312 : ((277167860557/5000000000000 : ℚ) : ℝ) ≤ stT339o2 312 := by
  have hc : ((979153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((312 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277167860557/5000000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((979153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c313 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((733933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57462031/20000000 : ℚ) : ℝ) ≤ Real.log ((313 : ℕ)) / 2 := by
    have h := (log_br_313).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((313 : ℕ)) / 2 ≤ ((3591377/1250000 : ℚ) : ℝ) := by
    have h := (log_br_313).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1866753/10000000) (δ := 8589/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t313 : ((414814889739/10000000000000 : ℚ) : ℝ) ≤ stT339o2 313 := by
  have hc : ((733883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((313 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).1
  have hw2 : ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((565233/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((414814889739/10000000000000 : ℚ) : ℝ)
      = ((565233/10000000 : ℚ) : ℝ) * ((733883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c314 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((55929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57493929/20000000 : ℚ) : ℝ) ≤ Real.log ((314 : ℕ)) / 2 := by
    have h := (log_br_314).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((314 : ℕ)) / 2 ≤ ((5749393/2000000 : ℚ) : ℝ) := by
    have h := (log_br_314).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3218431/10000000) (δ := 8489/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t314 : ((7889220277/500000000000 : ℚ) : ℝ) ≤ stT339o2 314 := by
  have hc : ((55919/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((314 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7889220277/500000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((55919/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c315 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-252763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28762863/10000000 : ℚ) : ℝ) ≤ Real.log ((315 : ℕ)) / 2 := by
    have h := (log_br_315).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((315 : ℕ)) / 2 ≤ ((57525727/20000000 : ℚ) : ℝ) := by
    have h := (log_br_315).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4565829/10000000) (δ := 4257/500000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t315 : ((-142444198281/10000000000000 : ℚ) : ℝ) ≤ stT339o2 315 := by
  have hc : ((-252813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((315 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-142444198281/10000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-252813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c316 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-712309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28778711/10000000 : ℚ) : ℝ) ≤ Real.log ((316 : ℕ)) / 2 := by
    have h := (log_br_316).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((316 : ℕ)) / 2 ≤ ((57557423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_316).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5908947/10000000) (δ := 4257/500000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t316 : ((-25045830081/625000000000 : ℚ) : ℝ) ≤ stT339o2 316 := by
  have hc : ((-712359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((316 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).2
  have h0 : (0:ℝ) ≤ ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25045830081/625000000000 : ℚ) : ℝ)
      = ((35159/625000 : ℚ) : ℝ) * ((-712359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c317 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-485373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57589017/20000000 : ℚ) : ℝ) ≤ Real.log ((317 : ℕ)) / 2 := by
    have h := (log_br_317).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((317 : ℕ)) / 2 ≤ ((28794509/10000000 : ℚ) : ℝ) := by
    have h := (log_br_317).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1449557/2000000) (δ := 8489/1000000000) (ψ := -65899/100000) 339 155
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t317 : ((-17039168693/312500000000 : ℚ) : ℝ) ≤ stT339o2 317 := by
  have hc : ((-242699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((317 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).2
  have h0 : (0:ℝ) ≤ ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17039168693/312500000000 : ℚ) : ℝ)
      = ((70207/1250000 : ℚ) : ℝ) * ((-242699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c318 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-957849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57620513/20000000 : ℚ) : ℝ) ≤ Real.log ((318 : ℕ)) / 2 := by
    have h := (log_br_318).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((318 : ℕ)) / 2 ≤ ((28810257/10000000 : ℚ) : ℝ) := by
    have h := (log_br_318).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1425107/2000000) (δ := 2143/250000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t318 : ((-537163895927/10000000000000 : ℚ) : ℝ) ≤ stT339o2 318 := by
  have hc : ((-957899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((318 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537163895927/10000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-957899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c319 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-679603/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57651911/20000000 : ℚ) : ℝ) ≤ Real.log ((319 : ℕ)) / 2 := by
    have h := (log_br_319).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((319 : ℕ)) / 2 ≤ ((7206489/2500000 : ℚ) : ℝ) := by
    have h := (log_br_319).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1159009/2000000) (δ := 8481/1000000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t319 : ((-380532957129/10000000000000 : ℚ) : ℝ) ≤ stT339o2 319 := by
  have hc : ((-679653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((319 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-380532957129/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-679653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c320 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-53757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57683209/20000000 : ℚ) : ℝ) ≤ Real.log ((320 : ℕ)) / 2 := by
    have h := (log_br_320).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((320 : ℕ)) / 2 ≤ ((5768321/2000000 : ℚ) : ℝ) := by
    have h := (log_br_320).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -558599/1250000) (δ := 2143/250000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t320 : ((-60116129163/5000000000000 : ℚ) : ℝ) ≤ stT339o2 320 := by
  have hc : ((-107539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((320 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60116129163/5000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-107539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c321 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((307109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57714411/20000000 : ℚ) : ℝ) ≤ Real.log ((321 : ℕ)) / 2 := by
    have h := (log_br_321).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((321 : ℕ)) / 2 ≤ ((14428603/5000000 : ℚ) : ℝ) := by
    have h := (log_br_321).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3146607/10000000) (δ := 271/31250000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t321 : ((34276689111/2000000000000 : ℚ) : ℝ) ≤ stT339o2 321 := by
  have hc : ((307059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((321 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).1
  have hw2 : ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111629/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34276689111/2000000000000 : ℚ) : ℝ)
      = ((111629/2000000 : ℚ) : ℝ) * ((307059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c322 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((37211/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11549103/4000000 : ℚ) : ℝ) ≤ Real.log ((322 : ℕ)) / 2 := by
    have h := (log_br_322).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((322 : ℕ)) / 2 ≤ ((14436379/5000000 : ℚ) : ℝ) := by
    have h := (log_br_322).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -73143/400000) (δ := 271/31250000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t322 : ((20735478463/500000000000 : ℚ) : ℝ) ≤ stT339o2 322 := by
  have hc : ((74417/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((322 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20735478463/500000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((74417/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c323 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((978889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57776523/20000000 : ℚ) : ℝ) ≤ Real.log ((323 : ℕ)) / 2 := by
    have h := (log_br_323).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((323 : ℕ)) / 2 ≤ ((14444131/5000000 : ℚ) : ℝ) := by
    have h := (log_br_323).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -514611/10000000) (δ := 271/31250000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t323 : ((272319861673/5000000000000 : ℚ) : ℝ) ≤ stT339o2 323 := by
  have hc : ((978839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((323 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272319861673/5000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((978839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c324 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((949827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11561487/4000000 : ℚ) : ℝ) ≤ Real.log ((324 : ℕ)) / 2 := by
    have h := (log_br_324).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((324 : ℕ)) / 2 ≤ ((14451859/5000000 : ℚ) : ℝ) := by
    have h := (log_br_324).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 159057/2000000) (δ := 271/31250000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t324 : ((105530672247/2000000000000 : ℚ) : ℝ) ≤ stT339o2 324 := by
  have hc : ((949777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((324 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105530672247/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((949777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c325 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((667131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57838251/20000000 : ℚ) : ℝ) ≤ Real.log ((325 : ℕ)) / 2 := by
    have h := (log_br_325).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((325 : ℕ)) / 2 ≤ ((14459563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_325).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2101113/10000000) (δ := 271/31250000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t325 : ((3700298307/100000000000 : ℚ) : ℝ) ≤ stT339o2 325 := by
  have hc : ((667081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((325 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3700298307/100000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((667081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c326 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((104041/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57868973/20000000 : ℚ) : ℝ) ≤ Real.log ((326 : ℕ)) / 2 := by
    have h := (log_br_326).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((326 : ℕ)) / 2 ≤ ((28934487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_326).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3402957/10000000) (δ := 8581/1000000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t326 : ((450070731/39062500000 : ℚ) : ℝ) ≤ stT339o2 326 := by
  have hc : ((6501/31250 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((326 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450070731/39062500000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((6501/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c327 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-76153/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57899601/20000000 : ℚ) : ℝ) ≤ Real.log ((327 : ℕ)) / 2 := by
    have h := (log_br_327).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((327 : ℕ)) / 2 ≤ ((28949801/10000000 : ℚ) : ℝ) := by
    have h := (log_br_327).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4700819/10000000) (δ := 2143/250000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t327 : ((-42119673831/2500000000000 : ℚ) : ℝ) ≤ stT339o2 327 := by
  have hc : ((-152331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((327 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42119673831/2500000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-152331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c328 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-735971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7241267/2500000 : ℚ) : ℝ) ≤ Real.log ((328 : ℕ)) / 2 := by
    have h := (log_br_328).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((328 : ℕ)) / 2 ≤ ((57930137/20000000 : ℚ) : ℝ) := by
    have h := (log_br_328).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5994739/10000000) (δ := 8631/1000000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t328 : ((-203199941659/5000000000000 : ℚ) : ℝ) ≤ stT339o2 328 := by
  have hc : ((-736021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((328 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203199941659/5000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-736021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c329 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-974183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((57960577/20000000 : ℚ) : ℝ) ≤ Real.log ((329 : ℕ)) / 2 := by
    have h := (log_br_329).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((329 : ℕ)) / 2 ≤ ((28980289/10000000 : ℚ) : ℝ) := by
    have h := (log_br_329).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7284677/10000000) (δ := 2143/250000000) (ψ := -65899/100000) 339 156
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t329 : ((-268556094547/5000000000000 : ℚ) : ℝ) ≤ stT339o2 329 := by
  have hc : ((-974233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((329 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268556094547/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-974233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c330 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-59949/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28995463/10000000 : ℚ) : ℝ) ≤ Real.log ((330 : ℕ)) / 2 := by
    have h := (log_br_330).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((330 : ℕ)) / 2 ≤ ((57990927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_330).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -223039/312500) (δ := 539/62500000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t330 : ((-132010262697/2500000000000 : ℚ) : ℝ) ≤ stT339o2 330 := by
  have hc : ((-479617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((330 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132010262697/2500000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-479617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c331 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-69703/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58021183/20000000 : ℚ) : ℝ) ≤ Real.log ((331 : ℕ)) / 2 := by
    have h := (log_br_331).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((331 : ℕ)) / 2 ≤ ((906581/312500 : ℚ) : ℝ) := by
    have h := (log_br_331).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5855107/10000000) (δ := 8579/1000000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t331 : ((-191575011/5000000000 : ℚ) : ℝ) ≤ stT339o2 331 := by
  have hc : ((-17427/25000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((331 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191575011/5000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-17427/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c332 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-32127/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58051349/20000000 : ℚ) : ℝ) ≤ Real.log ((332 : ℕ)) / 2 := by
    have h := (log_br_332).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((332 : ℕ)) / 2 ≤ ((1161027/400000 : ℚ) : ℝ) := by
    have h := (log_br_332).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4576823/10000000) (δ := 8479/1000000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t332 : ((-35270869063/2500000000000 : ℚ) : ℝ) ≤ stT339o2 332 := by
  have hc : ((-128533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((332 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35270869063/2500000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-128533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c333 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((247247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3630089/1250000 : ℚ) : ℝ) ≤ Real.log ((333 : ℕ)) / 2 := by
    have h := (log_br_333).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((333 : ℕ)) / 2 ≤ ((2323257/800000 : ℚ) : ℝ) := by
    have h := (log_br_333).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -660479/2000000) (δ := 2131/250000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t333 : ((33865741803/2500000000000 : ℚ) : ℝ) ≤ stT339o2 333 := by
  have hc : ((247197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((333 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33865741803/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((247197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c334 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((687531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58111409/20000000 : ℚ) : ℝ) ≤ Real.log ((334 : ℕ)) / 2 := by
    have h := (log_br_334).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((334 : ℕ)) / 2 ≤ ((5811141/2000000 : ℚ) : ℝ) := by
    have h := (log_br_334).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2031781/10000000) (δ := 4337/500000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t334 : ((15046896647/400000000000 : ℚ) : ℝ) ≤ stT339o2 334 := by
  have hc : ((687481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((334 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15046896647/400000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((687481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c335 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((476777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11628261/4000000 : ℚ) : ℝ) ≤ Real.log ((335 : ℕ)) / 2 := by
    have h := (log_br_335).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((335 : ℕ)) / 2 ≤ ((29070653/10000000 : ℚ) : ℝ) := by
    have h := (log_br_335).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -382469/5000000) (δ := 4337/500000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t335 : ((8139914663/156250000000 : ℚ) : ℝ) ≤ stT339o2 335 := by
  have hc : ((29797/31250 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((335 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8139914663/156250000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((29797/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c336 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((490109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58171111/20000000 : ℚ) : ℝ) ≤ Real.log ((336 : ℕ)) / 2 := by
    have h := (log_br_336).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((336 : ℕ)) / 2 ≤ ((7271389/2500000 : ℚ) : ℝ) := by
    have h := (log_br_336).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 124523/2500000) (δ := 8579/1000000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t336 : ((8355074553/156250000000 : ℚ) : ℝ) ≤ stT339o2 336 := by
  have hc : ((122521/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((336 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8355074553/156250000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((122521/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c337 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((381467/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58200829/20000000 : ℚ) : ℝ) ≤ Real.log ((337 : ℕ)) / 2 := by
    have h := (log_br_337).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((337 : ℕ)) / 2 ≤ ((5820083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_337).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 109837/625000) (δ := 8479/1000000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t337 : ((51946106607/1250000000000 : ℚ) : ℝ) ≤ stT339o2 337 := by
  have hc : ((190721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((337 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51946106607/1250000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((190721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c338 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((11173/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29115229/10000000 : ℚ) : ℝ) ≤ Real.log ((338 : ℕ)) / 2 := by
    have h := (log_br_338).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((338 : ℕ)) / 2 ≤ ((58230459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_338).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3012921/10000000) (δ := 8529/1000000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t338 : ((12152915313/625000000000 : ℚ) : ℝ) ≤ stT339o2 338 := by
  have hc : ((178743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((338 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).1
  have hw2 : ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67991/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12152915313/625000000000 : ℚ) : ℝ)
      = ((67991/1250000 : ℚ) : ℝ) * ((178743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c339 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-26943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58260001/20000000 : ℚ) : ℝ) ≤ Real.log ((339 : ℕ)) / 2 := by
    have h := (log_br_339).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((339 : ℕ)) / 2 ≤ ((29130001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_339).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 852961/2000000) (δ := 4337/500000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t339 : ((-7319437539/1000000000000 : ℚ) : ℝ) ≤ stT339o2 339 := by
  have hc : ((-26953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((339 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7319437539/1000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-26953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c340 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-118537/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3643091/1250000 : ℚ) : ℝ) ≤ Real.log ((340 : ℕ)) / 2 := by
    have h := (log_br_340).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((340 : ℕ)) / 2 ≤ ((58289457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_340).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5512961/10000000) (δ := 2131/250000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t340 : ((-64291238869/2000000000000 : ℚ) : ℝ) ≤ stT339o2 340 := by
  have hc : ((-118547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((340 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64291238869/2000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-118547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c341 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-452669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7289853/2500000 : ℚ) : ℝ) ≤ Real.log ((341 : ℕ)) / 2 := by
    have h := (log_br_341).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((341 : ℕ)) / 2 ≤ ((2332753/800000 : ℚ) : ℝ) := by
    have h := (log_br_341).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 675743/1000000) (δ := 2131/250000000) (ψ := -65899/100000) 339 157
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t341 : ((-122573917257/2500000000000 : ℚ) : ℝ) ≤ stT339o2 341 := by
  have hc : ((-226347/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((341 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122573917257/2500000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-226347/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c342 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-499167/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58348107/20000000 : ℚ) : ℝ) ≤ Real.log ((342 : ℕ)) / 2 := by
    have h := (log_br_342).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((342 : ℕ)) / 2 ≤ ((14587027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_342).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3854833/5000000) (δ := 4243/500000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t342 : ((-33741572861/625000000000 : ℚ) : ℝ) ≤ stT339o2 342 := by
  have hc : ((-62399/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((342 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33741572861/625000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-62399/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c343 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-170231/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7297163/2500000 : ℚ) : ℝ) ≤ Real.log ((343 : ℕ)) / 2 := by
    have h := (log_br_343).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((343 : ℕ)) / 2 ≤ ((11675461/4000000 : ℚ) : ℝ) := by
    have h := (log_br_343).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6472443/10000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t343 : ((-1838432559/40000000000 : ℚ) : ℝ) ≤ stT339o2 343 := by
  have hc : ((-170241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((343 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).2
  have h0 : (0:ℝ) ≤ ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1838432559/40000000000 : ℚ) : ℝ)
      = ((10799/200000 : ℚ) : ℝ) * ((-170241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c344 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-500981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3650401/1250000 : ℚ) : ℝ) ≤ Real.log ((344 : ℕ)) / 2 := by
    have h := (log_br_344).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((344 : ℕ)) / 2 ≤ ((58406417/20000000 : ℚ) : ℝ) := by
    have h := (log_br_344).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2619411/5000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t344 : ((-67534469521/2500000000000 : ℚ) : ℝ) ≤ stT339o2 344 := by
  have hc : ((-501031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((344 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67534469521/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-501031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c345 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-16351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14608861/5000000 : ℚ) : ℝ) ≤ Real.log ((345 : ℕ)) / 2 := by
    have h := (log_br_345).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((345 : ℕ)) / 2 ≤ ((11687089/4000000 : ℚ) : ℝ) := by
    have h := (log_br_345).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4008761/10000000) (δ := 8617/1000000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t345 : ((-551033977/312500000000 : ℚ) : ℝ) ≤ stT339o2 345 := by
  have hc : ((-2047/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((345 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551033977/312500000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-2047/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c346 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((110511/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58464387/20000000 : ℚ) : ℝ) ≤ Real.log ((346 : ℕ)) / 2 := by
    have h := (log_br_346).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((346 : ℕ)) / 2 ≤ ((14616097/5000000 : ℚ) : ℝ) := by
    have h := (log_br_346).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2782301/10000000) (δ := 4243/500000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t346 : ((118808650191/5000000000000 : ℚ) : ℝ) ≤ stT339o2 346 := by
  have hc : ((220997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((346 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118808650191/5000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((220997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c347 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((405849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58493247/20000000 : ℚ) : ℝ) ≤ Real.log ((347 : ℕ)) / 2 := by
    have h := (log_br_347).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((347 : ℕ)) / 2 ≤ ((913957/312500 : ℚ) : ℝ) := by
    have h := (log_br_347).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1559359/10000000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t347 : ((851006587/19531250000 : ℚ) : ℝ) ≤ stT339o2 347 := by
  have hc : ((12682/15625 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((347 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((851006587/19531250000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((12682/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c348 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((99077/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7315253/2500000 : ℚ) : ℝ) ≤ Real.log ((348 : ℕ)) / 2 := by
    have h := (log_br_348).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((348 : ℕ)) / 2 ≤ ((2340881/800000 : ℚ) : ℝ) := by
    have h := (log_br_348).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -339933/10000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t348 : ((25931709/488281250 : ℚ) : ℝ) ≤ stT339o2 348 := by
  have hc : ((3096/3125 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((348 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25931709/488281250 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((3096/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c349 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((939233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58550719/20000000 : ℚ) : ℝ) ≤ Real.log ((349 : ℕ)) / 2 := by
    have h := (log_br_349).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((349 : ℕ)) / 2 ≤ ((182971/62500 : ℚ) : ℝ) := by
    have h := (log_br_349).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 876017/10000000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t349 : ((502732450521/10000000000000 : ℚ) : ℝ) ≤ stT339o2 349 := by
  have hc : ((939183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((349 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((502732450521/10000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((939183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c350 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((41931/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58579331/20000000 : ℚ) : ℝ) ≤ Real.log ((350 : ℕ)) / 2 := by
    have h := (log_br_350).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((350 : ℕ)) / 2 ≤ ((14644833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_350).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2088451/10000000) (δ := 4243/500000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t350 : ((89645486403/2500000000000 : ℚ) : ℝ) ≤ stT339o2 350 := by
  have hc : ((335423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((350 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89645486403/2500000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((335423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c351 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((249163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29303931/10000000 : ℚ) : ℝ) ≤ Real.log ((351 : ℕ)) / 2 := by
    have h := (log_br_351).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((351 : ℕ)) / 2 ≤ ((58607863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_351).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 824363/2500000) (δ := 8517/1000000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t351 : ((103880121/7812500000 : ℚ) : ℝ) ≤ stT339o2 351 := by
  have hc : ((249113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((351 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103880121/7812500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((249113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c352 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-114181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58636311/20000000 : ℚ) : ℝ) ≤ Real.log ((352 : ℕ)) / 2 := by
    have h := (log_br_352).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((352 : ℕ)) / 2 ≤ ((7329539/2500000 : ℚ) : ℝ) := by
    have h := (log_br_352).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2251489/5000000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t352 : ((-15218006603/1250000000000 : ℚ) : ℝ) ≤ stT339o2 352 := by
  have hc : ((-57103/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((352 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15218006603/1250000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-57103/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c353 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-652781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1466617/500000 : ℚ) : ℝ) ≤ Real.log ((353 : ℕ)) / 2 := by
    have h := (log_br_353).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((353 : ℕ)) / 2 ≤ ((58664681/20000000 : ℚ) : ℝ) := by
    have h := (log_br_353).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1141023/2000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t353 : ((-347467341257/10000000000000 : ℚ) : ℝ) ≤ stT339o2 353 := by
  have hc : ((-652831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((353 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347467341257/10000000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-652831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c354 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-928647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58692969/20000000 : ℚ) : ℝ) ≤ Real.log ((354 : ℕ)) / 2 := by
    have h := (log_br_354).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((354 : ℕ)) / 2 ≤ ((5869297/2000000 : ℚ) : ℝ) := by
    have h := (log_br_354).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6903861/10000000) (δ := 8567/1000000000) (ψ := -65899/100000) 339 158
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t354 : ((-98719562403/2000000000000 : ℚ) : ℝ) ≤ stT339o2 354 := by
  have hc : ((-928697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((354 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98719562403/2000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-928697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c355 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-497597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58721177/20000000 : ℚ) : ℝ) ≤ Real.log ((355 : ℕ)) / 2 := by
    have h := (log_br_355).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((355 : ℕ)) / 2 ≤ ((29360589/10000000 : ℚ) : ℝ) := by
    have h := (log_br_355).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1902197/2500000) (δ := 8493/1000000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t355 : ((-26411038839/500000000000 : ℚ) : ℝ) ≤ stT339o2 355 := by
  have hc : ((-248811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((355 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26411038839/500000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-248811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c356 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-839257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58749307/20000000 : ℚ) : ℝ) ≤ Real.log ((356 : ℕ)) / 2 := by
    have h := (log_br_356).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((356 : ℕ)) / 2 ≤ ((14687327/5000000 : ℚ) : ℝ) := by
    have h := (log_br_356).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6416779/10000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t356 : ((-444831870693/10000000000000 : ℚ) : ℝ) ≤ stT339o2 356 := by
  have hc : ((-839307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((356 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444831870693/10000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-839307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c357 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-248643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58777357/20000000 : ℚ) : ℝ) ≤ Real.log ((357 : ℕ)) / 2 := by
    have h := (log_br_357).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((357 : ℕ)) / 2 ≤ ((29388679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_357).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5228161/10000000) (δ := 433/50000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t357 : ((-32902319919/1250000000000 : ℚ) : ℝ) ≤ stT339o2 357 := by
  have hc : ((-62167/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((357 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32902319919/1250000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-62167/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c358 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-23163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58805329/20000000 : ℚ) : ℝ) ≤ Real.log ((358 : ℕ)) / 2 := by
    have h := (log_br_358).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((358 : ℕ)) / 2 ≤ ((5880533/2000000 : ℚ) : ℝ) := by
    have h := (log_br_358).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4042847/10000000) (δ := 8493/1000000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t358 : ((-3063813049/1250000000000 : ℚ) : ℝ) ≤ stT339o2 358 := by
  have hc : ((-5797/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((358 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3063813049/1250000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-5797/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c359 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((413651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58833223/20000000 : ℚ) : ℝ) ≤ Real.log ((359 : ℕ)) / 2 := by
    have h := (log_br_359).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((359 : ℕ)) / 2 ≤ ((7354153/2500000 : ℚ) : ℝ) := by
    have h := (log_br_359).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2860839/10000000) (δ := 107/12500000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t359 : ((218289922179/10000000000000 : ℚ) : ℝ) ≤ stT339o2 359 := by
  have hc : ((413601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((359 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218289922179/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((413601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c360 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((782057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((735763/250000 : ℚ) : ℝ) ≤ Real.log ((360 : ℕ)) / 2 := by
    have h := (log_br_360).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((360 : ℕ)) / 2 ≤ ((58861041/20000000 : ℚ) : ℝ) := by
    have h := (log_br_360).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1682093/10000000) (δ := 8643/1000000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t360 : ((206076830661/5000000000000 : ℚ) : ℝ) ≤ stT339o2 360 := by
  have hc : ((782007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((360 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206076830661/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((782007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c361 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((489767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58888779/20000000 : ℚ) : ℝ) ≤ Real.log ((361 : ℕ)) / 2 := by
    have h := (log_br_361).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((361 : ℕ)) / 2 ≤ ((2944439/1000000 : ℚ) : ℝ) := by
    have h := (log_br_361).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -506653/10000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t361 : ((25775856073/500000000000 : ℚ) : ℝ) ≤ stT339o2 361 := by
  have hc : ((244871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((361 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25775856073/500000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((244871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c362 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((964771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29458221/10000000 : ℚ) : ℝ) ≤ Real.log ((362 : ℕ)) / 2 := by
    have h := (log_br_362).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((362 : ℕ)) / 2 ≤ ((58916443/20000000 : ℚ) : ℝ) := by
    have h := (log_br_362).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 332783/5000000) (δ := 861/100000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t362 : ((126761445237/2500000000000 : ℚ) : ℝ) ≤ stT339o2 362 := by
  have hc : ((964721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((362 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126761445237/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((964721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c363 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((742629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14736007/5000000 : ℚ) : ℝ) ≤ Real.log ((363 : ℕ)) / 2 := by
    have h := (log_br_363).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((363 : ℕ)) / 2 ≤ ((58944029/20000000 : ℚ) : ℝ) := by
    have h := (log_br_363).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1834523/10000000) (δ := 851/100000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t363 : ((389752241677/10000000000000 : ℚ) : ℝ) ≤ stT339o2 363 := by
  have hc : ((742579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((363 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((389752241677/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((742579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c364 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((362261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29485769/10000000 : ℚ) : ℝ) ≤ Real.log ((364 : ℕ)) / 2 := by
    have h := (log_br_364).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((364 : ℕ)) / 2 ≤ ((58971539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_364).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3000259/10000000) (δ := 861/100000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t364 : ((94924998981/5000000000000 : ℚ) : ℝ) ≤ stT339o2 364 := by
  have hc : ((362211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((364 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94924998981/5000000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((362211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c365 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-94191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((58998973/20000000 : ℚ) : ℝ) ≤ Real.log ((365 : ℕ)) / 2 := by
    have h := (log_br_365).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((365 : ℕ)) / 2 ≤ ((29499487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_365).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4162817/10000000) (δ := 433/50000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t365 : ((-1541500037/312500000000 : ℚ) : ℝ) ≤ stT339o2 365 := by
  have hc : ((-94241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((365 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1541500037/312500000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-94241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c366 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-529561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59026333/20000000 : ℚ) : ℝ) ≤ Real.log ((366 : ℕ)) / 2 := by
    have h := (log_br_366).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((366 : ℕ)) / 2 ≤ ((29513167/10000000 : ℚ) : ℝ) := by
    have h := (log_br_366).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5322197/10000000) (δ := 433/50000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t366 : ((-276832436199/10000000000000 : ℚ) : ℝ) ≤ stT339o2 366 := by
  have hc : ((-529611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((366 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-276832436199/10000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-529611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c367 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-852403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29526809/10000000 : ℚ) : ℝ) ≤ Real.log ((367 : ℕ)) / 2 := by
    have h := (log_br_367).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((367 : ℕ)) / 2 ≤ ((59053619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_367).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6478399/10000000) (δ := 861/100000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t367 : ((-111244264047/2500000000000 : ℚ) : ℝ) ≤ stT339o2 367 := by
  have hc : ((-852453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((367 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111244264047/2500000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-852453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c368 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-498021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59080829/20000000 : ℚ) : ℝ) ≤ Real.log ((368 : ℕ)) / 2 := by
    have h := (log_br_368).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((368 : ℕ)) / 2 ≤ ((5908083/2000000 : ℚ) : ℝ) := by
    have h := (log_br_368).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1526293/2000000) (δ := 433/50000000) (ψ := -65899/100000) 339 159
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t368 : ((-129812452601/2500000000000 : ℚ) : ℝ) ≤ stT339o2 368 := by
  have hc : ((-249023/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((368 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129812452601/2500000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-249023/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c369 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-465989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29553983/10000000 : ℚ) : ℝ) ≤ Real.log ((369 : ℕ)) / 2 := by
    have h := (log_br_369).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((369 : ℕ)) / 2 ≤ ((59107967/20000000 : ℚ) : ℝ) := by
    have h := (log_br_369).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6926567/10000000) (δ := 173/20000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t369 : ((-6064939203/125000000000 : ℚ) : ℝ) ≤ stT339o2 369 := by
  have hc : ((-233007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((369 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6064939203/125000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-233007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c370 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-675097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5913503/2000000 : ℚ) : ℝ) ≤ Real.log ((370 : ℕ)) / 2 := by
    have h := (log_br_370).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((370 : ℕ)) / 2 ≤ ((59135031/20000000 : ℚ) : ℝ) := by
    have h := (log_br_370).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -577973/1000000) (δ := 173/20000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t370 : ((-87748180443/2500000000000 : ℚ) : ℝ) ≤ stT339o2 370 := by
  have hc : ((-675147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((370 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87748180443/2500000000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-675147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c371 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-69957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2958101/1000000 : ℚ) : ℝ) ≤ Real.log ((371 : ℕ)) / 2 := by
    have h := (log_br_371).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((371 : ℕ)) / 2 ≤ ((59162021/20000000 : ℚ) : ℝ) := by
    have h := (log_br_371).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4636029/10000000) (δ := 171/20000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t371 : ((-2906113213/200000000000 : ℚ) : ℝ) ≤ stT339o2 371 := by
  have hc : ((-139939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((371 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2906113213/200000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-139939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c372 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((42947/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29594469/10000000 : ℚ) : ℝ) ≤ Real.log ((372 : ℕ)) / 2 := by
    have h := (log_br_372).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((372 : ℕ)) / 2 ≤ ((59188939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_372).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3495379/10000000) (δ := 8503/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t372 : ((1780837191/200000000000 : ℚ) : ℝ) ≤ stT339o2 372 := by
  have hc : ((85869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((372 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1780837191/200000000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((85869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c373 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((73409/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7401973/2500000 : ℚ) : ℝ) ≤ Real.log ((373 : ℕ)) / 2 := by
    have h := (log_br_373).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((373 : ℕ)) / 2 ≤ ((11843157/4000000 : ℚ) : ℝ) := by
    have h := (log_br_373).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -117889/500000) (δ := 8603/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t373 : ((7601295179/250000000000 : ℚ) : ℝ) ≤ stT339o2 373 := by
  have hc : ((293611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((373 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).1
  have hw2 : ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25889/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7601295179/250000000000 : ℚ) : ℝ)
      = ((25889/500000 : ℚ) : ℝ) * ((293611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c374 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((441329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59242557/20000000 : ℚ) : ℝ) ≤ Real.log ((374 : ℕ)) / 2 := by
    have h := (log_br_374).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((374 : ℕ)) / 2 ≤ ((29621279/10000000 : ℚ) : ℝ) := by
    have h := (log_br_374).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -611637/5000000) (δ := 8553/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t374 : ((28524070181/625000000000 : ℚ) : ℝ) ≤ stT339o2 374 := by
  have hc : ((55163/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((374 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28524070181/625000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((55163/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c375 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((999327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2963463/1000000 : ℚ) : ℝ) ≤ Real.log ((375 : ℕ)) / 2 := by
    have h := (log_br_375).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((375 : ℕ)) / 2 ≤ ((59269261/20000000 : ℚ) : ℝ) := by
    have h := (log_br_375).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -45867/5000000) (δ := 171/20000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t375 : ((516023644969/10000000000000 : ℚ) : ℝ) ≤ stT339o2 375 := by
  have hc : ((999277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((375 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516023644969/10000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((999277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c376 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((915237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59295891/20000000 : ℚ) : ℝ) ≤ Real.log ((376 : ℕ)) / 2 := by
    have h := (log_br_376).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((376 : ℕ)) / 2 ≤ ((14823973/5000000 : ℚ) : ℝ) := by
    have h := (log_br_376).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 518377/5000000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t376 : ((47197108777/1000000000000 : ℚ) : ℝ) ≤ stT339o2 376 := by
  have hc : ((915187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((376 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47197108777/1000000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((915187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c377 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((648721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59322451/20000000 : ℚ) : ℝ) ≤ Real.log ((377 : ℕ)) / 2 := by
    have h := (log_br_377).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((377 : ℕ)) / 2 ≤ ((14830613/5000000 : ℚ) : ℝ) := by
    have h := (log_br_377).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1081117/5000000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t377 : ((167041215223/5000000000000 : ℚ) : ℝ) ≤ stT339o2 377 := by
  have hc : ((648671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((377 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167041215223/5000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((648671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c378 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((254081/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59348941/20000000 : ℚ) : ℝ) ≤ Real.log ((378 : ℕ)) / 2 := by
    have h := (log_br_378).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((378 : ℕ)) / 2 ≤ ((29674471/10000000 : ℚ) : ℝ) := by
    have h := (log_br_378).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 821187/2500000) (δ := 8553/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t378 : ((16332415083/1250000000000 : ℚ) : ℝ) ≤ stT339o2 378 := by
  have hc : ((254031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((378 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16332415083/1250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((254031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c379 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-189781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29687681/10000000 : ℚ) : ℝ) ≤ Real.log ((379 : ℕ)) / 2 := by
    have h := (log_br_379).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((379 : ℕ)) / 2 ≤ ((59375363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_379).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2202169/5000000) (δ := 8503/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t379 : ((-48754865223/5000000000000 : ℚ) : ℝ) ≤ stT339o2 379 := by
  have hc : ((-189831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((379 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).2
  have h0 : (0:ℝ) ≤ ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48754865223/5000000000000 : ℚ) : ℝ)
      = ((256833/5000000 : ℚ) : ℝ) * ((-189831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c380 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-297623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3712607/1250000 : ℚ) : ℝ) ≤ Real.log ((380 : ℕ)) / 2 := by
    have h := (log_br_380).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((380 : ℕ)) / 2 ≤ ((59401713/20000000 : ℚ) : ℝ) := by
    have h := (log_br_380).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5520919/10000000) (δ := 8603/1000000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t380 : ((-954315297/31250000000 : ℚ) : ℝ) ≤ stT339o2 380 := by
  have hc : ((-18603/31250 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((380 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-954315297/31250000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-18603/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c381 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-110423/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59427993/20000000 : ℚ) : ℝ) ≤ Real.log ((381 : ℕ)) / 2 := by
    have h := (log_br_381).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((381 : ℕ)) / 2 ≤ ((29713997/10000000 : ℚ) : ℝ) := by
    have h := (log_br_381).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6634577/10000000) (δ := 43/5000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t381 : ((-56574671643/1250000000000 : ℚ) : ℝ) ≤ stT339o2 381 := by
  have hc : ((-441717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((381 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56574671643/1250000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-441717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c382 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-62441/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29727103/10000000 : ℚ) : ℝ) ≤ Real.log ((382 : ℕ)) / 2 := by
    have h := (log_br_382).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((382 : ℕ)) / 2 ≤ ((59454207/20000000 : ℚ) : ℝ) := by
    have h := (log_br_382).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7745353/10000000) (δ := 173/20000000) (ψ := -65899/100000) 339 160
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t382 : ((-51118758937/1000000000000 : ℚ) : ℝ) ≤ stT339o2 382 := by
  have hc : ((-499553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((382 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51118758937/1000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-499553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c383 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-921189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59480349/20000000 : ℚ) : ℝ) ≤ Real.log ((383 : ℕ)) / 2 := by
    have h := (log_br_383).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((383 : ℕ)) / 2 ≤ ((1189607/400000 : ℚ) : ℝ) := by
    have h := (log_br_383).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6854801/10000000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t383 : ((-470731940503/10000000000000 : ℚ) : ℝ) ≤ stT339o2 383 := by
  have hc : ((-921239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((383 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-470731940503/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-921239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c384 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-333113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2380257/800000 : ℚ) : ℝ) ≤ Real.log ((384 : ℕ)) / 2 := by
    have h := (log_br_384).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((384 : ℕ)) / 2 ≤ ((29753213/10000000 : ℚ) : ℝ) := by
    have h := (log_br_384).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5749831/10000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t384 : ((-85001992959/2500000000000 : ℚ) : ℝ) ≤ stT339o2 384 := by
  have hc : ((-166569/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((384 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85001992959/2500000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-166569/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c385 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-284323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59532433/20000000 : ℚ) : ℝ) ≤ Real.log ((385 : ℕ)) / 2 := by
    have h := (log_br_385).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((385 : ℕ)) / 2 ≤ ((29766217/10000000 : ℚ) : ℝ) := by
    have h := (log_br_385).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2323871/5000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t385 : ((-9058133169/625000000000 : ℚ) : ℝ) ≤ stT339o2 385 := by
  have hc : ((-284373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((385 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9058133169/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-284373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c386 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((30161/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59558373/20000000 : ℚ) : ℝ) ≤ Real.log ((386 : ℕ)) / 2 := by
    have h := (log_br_386).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((386 : ℕ)) / 2 ≤ ((29779187/10000000 : ℚ) : ℝ) := by
    have h := (log_br_386).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1774267/5000000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t386 : ((7673218443/1000000000000 : ℚ) : ℝ) ≤ stT339o2 386 := by
  have hc : ((30151/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((386 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7673218443/1000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((30151/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c387 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((556303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29792123/10000000 : ℚ) : ℝ) ≤ Real.log ((387 : ℕ)) / 2 := by
    have h := (log_br_387).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((387 : ℕ)) / 2 ≤ ((59584247/20000000 : ℚ) : ℝ) := by
    have h := (log_br_387).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1226083/5000000) (δ := 2149/250000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t387 : ((35344871873/1250000000000 : ℚ) : ℝ) ≤ stT339o2 387 := by
  have hc : ((556253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((387 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35344871873/1250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((556253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c388 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((13374/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59610053/20000000 : ℚ) : ℝ) ≤ Real.log ((388 : ℕ)) / 2 := by
    have h := (log_br_388).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((388 : ℕ)) / 2 ≤ ((29805027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_388).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -679297/5000000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t388 : ((217255106639/5000000000000 : ℚ) : ℝ) ≤ stT339o2 388 := by
  have hc : ((427943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((388 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217255106639/5000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((427943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c389 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((198853/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59635793/20000000 : ℚ) : ℝ) ≤ Real.log ((389 : ℕ)) / 2 := by
    have h := (log_br_389).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((389 : ℕ)) / 2 ≤ ((29817897/10000000 : ℚ) : ℝ) := by
    have h := (log_br_389).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -133931/5000000) (δ := 4323/500000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t389 : ((5040868893/100000000000 : ℚ) : ℝ) ≤ stT339o2 389 := by
  have hc : ((198843/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((389 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5040868893/100000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((198843/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c390 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((946679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59661467/20000000 : ℚ) : ℝ) ≤ Real.log ((390 : ℕ)) / 2 := by
    have h := (log_br_390).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((390 : ℕ)) / 2 ≤ ((14915367/5000000 : ℚ) : ℝ) := by
    have h := (log_br_390).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 410037/5000000) (δ := 4273/500000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t390 : ((479343580101/10000000000000 : ℚ) : ℝ) ≤ stT339o2 390 := by
  have hc : ((946629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((390 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((479343580101/10000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((946629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c391 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((361699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2387483/800000 : ℚ) : ℝ) ≤ Real.log ((391 : ℕ)) / 2 := by
    have h := (log_br_391).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((391 : ℕ)) / 2 ≤ ((14921769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_391).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1905213/10000000) (δ := 4273/500000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t391 : ((91453068477/2500000000000 : ℚ) : ℝ) ≤ stT339o2 391 := by
  have hc : ((180837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((391 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91453068477/2500000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((180837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c392 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((366977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29856309/10000000 : ℚ) : ℝ) ≤ Real.log ((392 : ℕ)) / 2 := by
    have h := (log_br_392).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((392 : ℕ)) / 2 ≤ ((59712619/20000000 : ℚ) : ℝ) := by
    have h := (log_br_392).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1493799/5000000) (δ := 8557/1000000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t392 : ((46331505363/2500000000000 : ℚ) : ℝ) ≤ stT339o2 392 := by
  have hc : ((366927/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((392 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46331505363/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((366927/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c393 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-11213/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3733631/1250000 : ℚ) : ℝ) ≤ Real.log ((393 : ℕ)) / 2 := by
    have h := (log_br_393).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((393 : ℕ)) / 2 ≤ ((59738097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_393).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1016807/2500000) (δ := 531/62500000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t393 : ((-2830631391/1000000000000 : ℚ) : ℝ) ≤ stT339o2 393 := by
  have hc : ((-11223/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((393 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2830631391/1000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-11223/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c394 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-1462/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59763509/20000000 : ℚ) : ℝ) ≤ Real.log ((394 : ℕ)) / 2 := by
    have h := (log_br_394).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((394 : ℕ)) / 2 ≤ ((5976351/2000000 : ℚ) : ℝ) := by
    have h := (log_br_394).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 643013/1250000) (δ := 8507/1000000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t394 : ((-23571970677/1000000000000 : ℚ) : ℝ) ≤ stT339o2 394 := by
  have hc : ((-46789/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((394 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23571970677/1000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-46789/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c395 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-793473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((59788857/20000000 : ℚ) : ℝ) ≤ Real.log ((395 : ℕ)) / 2 := by
    have h := (log_br_395).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((395 : ℕ)) / 2 ≤ ((29894429/10000000 : ℚ) : ℝ) := by
    have h := (log_br_395).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 248729/400000) (δ := 4323/500000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t395 : ((-79853013013/2000000000000 : ℚ) : ℝ) ≤ stT339o2 395 := by
  have hc : ((-793523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((395 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79853013013/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-793523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c396 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-974633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29907071/10000000 : ℚ) : ℝ) ≤ Real.log ((396 : ℕ)) / 2 := by
    have h := (log_br_396).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((396 : ℕ)) / 2 ≤ ((59814143/20000000 : ℚ) : ℝ) := by
    have h := (log_br_396).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7289677/10000000) (δ := 2149/250000000) (ψ := -65899/100000) 339 161
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t396 : ((-489796726477/10000000000000 : ℚ) : ℝ) ≤ stT339o2 396 := by
  have hc : ((-974683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((396 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-489796726477/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-974683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c397 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-244929/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29919681/10000000 : ℚ) : ℝ) ≤ Real.log ((397 : ℕ)) / 2 := by
    have h := (log_br_397).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((397 : ℕ)) / 2 ≤ ((59839363/20000000 : ℚ) : ℝ) := by
    have h := (log_br_397).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1837397/2500000) (δ := 1733/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t397 : ((-122932709669/2500000000000 : ℚ) : ℝ) ≤ stT339o2 397 := by
  have hc : ((-489883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((397 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122932709669/2500000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-489883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c398 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-161819/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1496613/500000 : ℚ) : ℝ) ≤ Real.log ((398 : ℕ)) / 2 := by
    have h := (log_br_398).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((398 : ℕ)) / 2 ≤ ((59864521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_398).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3141759/5000000) (δ := 1713/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t398 : ((-16223519079/400000000000 : ℚ) : ℝ) ≤ stT339o2 398 := by
  have hc : ((-161829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((398 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16223519079/400000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-161829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c399 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-494507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29944807/10000000 : ℚ) : ℝ) ≤ Real.log ((399 : ℕ)) / 2 := by
    have h := (log_br_399).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((399 : ℕ)) / 2 ≤ ((11977923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_399).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -16313/31250) (δ := 1061/125000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t399 : ((-247588587239/10000000000000 : ℚ) : ℝ) ≤ stT339o2 399 := by
  have hc : ((-494557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((399 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).2
  have h0 : (0:ℝ) ≤ ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247588587239/10000000000000 : ℚ) : ℝ)
      = ((500627/10000000 : ℚ) : ℝ) * ((-494557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c400 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-46429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11982929/4000000 : ℚ) : ℝ) ≤ Real.log ((400 : ℕ)) / 2 := by
    have h := (log_br_400).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((400 : ℕ)) / 2 ≤ ((29957323/10000000 : ℚ) : ℝ) := by
    have h := (log_br_400).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4159471/10000000) (δ := 1723/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t400 : ((-11613523227/2500000000000 : ℚ) : ℝ) ≤ stT339o2 400 := by
  have hc : ((-23227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((400 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).2
  have h0 : (0:ℝ) ≤ ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11613523227/2500000000000 : ℚ) : ℝ)
      = ((500001/10000000 : ℚ) : ℝ) * ((-23227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c401 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((324263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29969807/10000000 : ℚ) : ℝ) ≤ Real.log ((401 : ℕ)) / 2 := by
    have h := (log_br_401).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((401 : ℕ)) / 2 ≤ ((11987923/4000000 : ℚ) : ℝ) := by
    have h := (log_br_401).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -310141/1000000) (δ := 1061/125000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t401 : ((10119011943/625000000000 : ℚ) : ℝ) ≤ stT339o2 401 := by
  have hc : ((324213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((401 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10119011943/625000000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((324213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c402 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((136677/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1499113/500000 : ℚ) : ℝ) ≤ Real.log ((402 : ℕ)) / 2 := by
    have h := (log_br_402).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((402 : ℕ)) / 2 ≤ ((59964521/20000000 : ℚ) : ℝ) := by
    have h := (log_br_402).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1023009/5000000) (δ := 1713/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t402 : ((34081606459/1000000000000 : ℚ) : ℝ) ≤ stT339o2 402 := by
  have hc : ((136667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((402 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34081606459/1000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((136667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c403 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((184423/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11997873/4000000 : ℚ) : ℝ) ≤ Real.log ((403 : ℕ)) / 2 := by
    have h := (log_br_403).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((403 : ℕ)) / 2 ≤ ((29994683/10000000 : ℚ) : ℝ) := by
    have h := (log_br_403).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -993211/10000000) (δ := 1723/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t403 : ((18372513951/400000000000 : ℚ) : ℝ) ≤ stT339o2 403 := by
  have hc : ((184413/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((403 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18372513951/400000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((184413/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c404 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((49987/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15003537/5000000 : ℚ) : ℝ) ≤ Real.log ((404 : ℕ)) / 2 := by
    have h := (log_br_404).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((404 : ℕ)) / 2 ≤ ((60014149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_404).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7121/1250000) (δ := 2147/250000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t404 : ((24868188471/500000000000 : ℚ) : ℝ) ≤ stT339o2 404 := by
  have hc : ((99969/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((404 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).1
  have hw2 : ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((248759/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24868188471/500000000000 : ℚ) : ℝ)
      = ((248759/5000000 : ℚ) : ℝ) * ((99969/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c405 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((903973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6003887/2000000 : ℚ) : ℝ) ≤ Real.log ((405 : ℕ)) / 2 := by
    have h := (log_br_405).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((405 : ℕ)) / 2 ≤ ((60038871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_405).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1104563/10000000) (δ := 1061/125000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t405 : ((449162050469/10000000000000 : ℚ) : ℝ) ≤ stT339o2 405 := by
  have hc : ((903923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((405 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).1
  have hw2 : ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496903/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449162050469/10000000000000 : ℚ) : ℝ)
      = ((496903/10000000 : ℚ) : ℝ) * ((903923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c406 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((652567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60063531/20000000 : ℚ) : ℝ) ≤ Real.log ((406 : ℕ)) / 2 := by
    have h := (log_br_406).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((406 : ℕ)) / 2 ≤ ((15015883/5000000 : ℚ) : ℝ) := by
    have h := (log_br_406).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2149573/10000000) (δ := 1703/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t406 : ((323838314447/10000000000000 : ℚ) : ℝ) ≤ stT339o2 406 := by
  have hc : ((652517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((406 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((323838314447/10000000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((652517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c407 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((14489/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60088131/20000000 : ℚ) : ℝ) ≤ Real.log ((407 : ℕ)) / 2 := by
    have h := (log_br_407).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((407 : ℕ)) / 2 ≤ ((15022033/5000000 : ℚ) : ℝ) := by
    have h := (log_br_407).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1595999/5000000) (δ := 1703/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t407 : ((14361365613/1000000000000 : ℚ) : ℝ) ≤ stT339o2 407 := by
  have hc : ((28973/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((407 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14361365613/1000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((28973/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c408 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-60827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60112671/20000000 : ℚ) : ℝ) ≤ Real.log ((408 : ℕ)) / 2 := by
    have h := (log_br_408).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((408 : ℕ)) / 2 ≤ ((1878521/625000 : ℚ) : ℝ) := by
    have h := (log_br_408).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 105797/250000) (δ := 4319/500000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t408 : ((-3765780381/625000000000 : ℚ) : ℝ) ≤ stT339o2 408 := by
  have hc : ((-15213/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((408 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3765780381/625000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-15213/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c409 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-511467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60137151/20000000 : ℚ) : ℝ) ≤ Real.log ((409 : ℕ)) / 2 := by
    have h := (log_br_409).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((409 : ℕ)) / 2 ≤ ((939643/312500 : ℚ) : ℝ) := by
    have h := (log_br_409).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 263461/500000) (δ := 4319/500000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t409 : ((-252929299473/10000000000000 : ℚ) : ℝ) ≤ stT339o2 409 := by
  have hc : ((-511517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((409 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).2
  have h0 : (0:ℝ) ≤ ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-252929299473/10000000000000 : ℚ) : ℝ)
      = ((494469/10000000 : ℚ) : ℝ) * ((-511517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c410 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-813887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60161571/20000000 : ℚ) : ℝ) ≤ Real.log ((410 : ℕ)) / 2 := by
    have h := (log_br_410).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((410 : ℕ)) / 2 ≤ ((15040393/5000000 : ℚ) : ℝ) := by
    have h := (log_br_410).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3152009/5000000) (δ := 1703/200000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t410 : ((-80394999301/2000000000000 : ℚ) : ℝ) ≤ stT339o2 410 := by
  have hc : ((-813937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((410 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80394999301/2000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-813937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c411 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-489319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15046483/5000000 : ℚ) : ℝ) ≤ Real.log ((411 : ℕ)) / 2 := by
    have h := (log_br_411).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((411 : ℕ)) / 2 ≤ ((60185933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_411).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1467263/2000000) (δ := 2147/250000000) (ψ := -65899/100000) 339 162
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t411 : ((-117859267/2441406250 : ℚ) : ℝ) ≤ stT339o2 411 := by
  have hc : ((-15292/15625 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((411 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117859267/2441406250 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-15292/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c412 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-489547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60210233/20000000 : ℚ) : ℝ) ≤ Real.log ((412 : ℕ)) / 2 := by
    have h := (log_br_412).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((412 : ℕ)) / 2 ≤ ((30105117/10000000 : ℚ) : ℝ) := by
    have h := (log_br_412).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7341893/10000000) (δ := 4261/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t412 : ((-12059749469/250000000000 : ℚ) : ℝ) ≤ stT339o2 412 := by
  have hc : ((-122393/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((412 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12059749469/250000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-122393/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c413 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-204087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2409379/800000 : ℚ) : ℝ) ≤ Real.log ((413 : ℕ)) / 2 := by
    have h := (log_br_413).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((413 : ℕ)) / 2 ≤ ((15058619/5000000 : ℚ) : ℝ) := by
    have h := (log_br_413).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3157319/5000000) (δ := 4311/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t413 : ((-50215416383/1250000000000 : ℚ) : ℝ) ≤ stT339o2 413 := by
  have hc : ((-408199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((413 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50215416383/1250000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-408199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c414 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-259269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60258659/20000000 : ℚ) : ℝ) ≤ Real.log ((414 : ℕ)) / 2 := by
    have h := (log_br_414).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((414 : ℕ)) / 2 ≤ ((3012933/1000000 : ℚ) : ℝ) := by
    have h := (log_br_414).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5289841/10000000) (δ := 4311/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t414 : ((-31859064839/1250000000000 : ℚ) : ℝ) ≤ stT339o2 414 := by
  have hc : ((-129647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((414 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).2
  have h0 : (0:ℝ) ≤ ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31859064839/1250000000000 : ℚ) : ℝ)
      = ((245737/5000000 : ℚ) : ℝ) * ((-129647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c415 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-16973/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12056557/4000000 : ℚ) : ℝ) ≤ Real.log ((415 : ℕ)) / 2 := by
    have h := (log_br_415).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((415 : ℕ)) / 2 ≤ ((30141393/10000000 : ℚ) : ℝ) := by
    have h := (log_br_415).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2133751/5000000) (δ := 4261/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t415 : ((-33339164877/5000000000000 : ℚ) : ℝ) ≤ stT339o2 415 := by
  have hc : ((-67917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((415 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33339164877/5000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-67917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c416 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((268399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15076713/5000000 : ℚ) : ℝ) ≤ Real.log ((416 : ℕ)) / 2 := by
    have h := (log_br_416).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((416 : ℕ)) / 2 ≤ ((60306853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_416).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3247663/10000000) (δ := 8481/1000000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t416 : ((13156883121/1000000000000 : ℚ) : ℝ) ≤ stT339o2 416 := by
  have hc : ((268349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((416 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13156883121/1000000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((268349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c417 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((313891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30165431/10000000 : ℚ) : ℝ) ≤ Real.log ((417 : ℕ)) / 2 := by
    have h := (log_br_417).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((417 : ℕ)) / 2 ≤ ((60330863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_417).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2230239/10000000) (δ := 2143/250000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t417 : ((38425201983/1250000000000 : ℚ) : ℝ) ≤ stT339o2 417 := by
  have hc : ((156933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((417 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38425201983/1250000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((156933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c418 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((884157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30177407/10000000 : ℚ) : ℝ) ≤ Real.log ((418 : ℕ)) / 2 := by
    have h := (log_br_418).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((418 : ℕ)) / 2 ≤ ((12070963/4000000 : ℚ) : ℝ) := by
    have h := (log_br_418).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1215273/10000000) (δ := 2143/250000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t418 : ((86485999061/2000000000000 : ℚ) : ℝ) ≤ stT339o2 418 := by
  have hc : ((884107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((418 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).1
  have hw2 : ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((97823/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86485999061/2000000000000 : ℚ) : ℝ)
      = ((97823/2000000 : ℚ) : ℝ) * ((884107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c419 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((498357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60378709/20000000 : ℚ) : ℝ) ≤ Real.log ((419 : ℕ)) / 2 := by
    have h := (log_br_419).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((419 : ℕ)) / 2 ≤ ((6037871/2000000 : ℚ) : ℝ) := by
    have h := (log_br_419).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -202723/10000000) (δ := 8631/1000000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t419 : ((60862657573/1250000000000 : ℚ) : ℝ) ≤ stT339o2 419 := by
  have hc : ((124583/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((419 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).1
  have hw2 : ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((488531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60862657573/1250000000000 : ℚ) : ℝ)
      = ((488531/10000000 : ℚ) : ℝ) * ((124583/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c420 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((474149/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60402547/20000000 : ℚ) : ℝ) ≤ Real.log ((420 : ℕ)) / 2 := by
    have h := (log_br_420).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((420 : ℕ)) / 2 ≤ ((15100637/5000000 : ℚ) : ℝ) := by
    have h := (log_br_420).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 807413/10000000) (δ := 4311/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t420 : ((1156744029/25000000000 : ℚ) : ℝ) ≤ stT339o2 420 := by
  have hc : ((118531/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((420 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1156744029/25000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((118531/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c421 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((747801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7553291/2500000 : ℚ) : ℝ) ≤ Real.log ((421 : ℕ)) / 2 := by
    have h := (log_br_421).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((421 : ℕ)) / 2 ≤ ((60426329/20000000 : ℚ) : ℝ) := by
    have h := (log_br_421).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1815133/10000000) (δ := 271/31250000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t421 : ((36443140487/1000000000000 : ℚ) : ℝ) ≤ stT339o2 421 := by
  have hc : ((747751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((421 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36443140487/1000000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((747751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c422 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((85659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60450053/20000000 : ℚ) : ℝ) ≤ Real.log ((422 : ℕ)) / 2 := by
    have h := (log_br_422).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((422 : ℕ)) / 2 ≤ ((30225027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_422).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2820479/10000000) (δ := 8631/1000000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t422 : ((5211656001/250000000000 : ℚ) : ℝ) ≤ stT339o2 422 := by
  have hc : ((85649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((422 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5211656001/250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((85649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c423 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((2071/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60473721/20000000 : ℚ) : ℝ) ≤ Real.log ((423 : ℕ)) / 2 := by
    have h := (log_br_423).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((423 : ℕ)) / 2 ≤ ((30236861/10000000 : ℚ) : ℝ) := by
    have h := (log_br_423).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3823411/10000000) (δ := 4261/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t423 : ((251434449/125000000000 : ℚ) : ℝ) ≤ stT339o2 423 := by
  have hc : ((4137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((423 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251434449/125000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((4137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c424 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-351159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30248667/10000000 : ℚ) : ℝ) ≤ Real.log ((424 : ℕ)) / 2 := by
    have h := (log_br_424).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((424 : ℕ)) / 2 ≤ ((12099467/4000000 : ℚ) : ℝ) := by
    have h := (log_br_424).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1206003/2500000) (δ := 2143/250000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t424 : ((-170562192387/10000000000000 : ℚ) : ℝ) ≤ stT339o2 424 := by
  have hc : ((-351209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((424 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).2
  have h0 : (0:ℝ) ≤ ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170562192387/10000000000000 : ℚ) : ℝ)
      = ((485643/10000000 : ℚ) : ℝ) * ((-351209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c425 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-687543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60520891/20000000 : ℚ) : ℝ) ≤ Real.log ((425 : ℕ)) / 2 := by
    have h := (log_br_425).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((425 : ℕ)) / 2 ≤ ((15130223/5000000 : ℚ) : ℝ) := by
    have h := (log_br_425).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 36389/62500) (δ := 4311/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t425 : ((-20845756981/625000000000 : ℚ) : ℝ) ≤ stT339o2 425 := by
  have hc : ((-687593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((425 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).2
  have h0 : (0:ℝ) ≤ ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20845756981/625000000000 : ℚ) : ℝ)
      = ((30317/625000 : ℚ) : ℝ) * ((-687593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c426 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-915383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60544393/20000000 : ℚ) : ℝ) ≤ Real.log ((426 : ℕ)) / 2 := by
    have h := (log_br_426).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((426 : ℕ)) / 2 ≤ ((30272197/10000000 : ℚ) : ℝ) := by
    have h := (log_br_426).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6818137/10000000) (δ := 4261/500000000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t426 : ((-221764559683/5000000000000 : ℚ) : ℝ) ≤ stT339o2 426 := by
  have hc : ((-915433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((426 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221764559683/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-915433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c427 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-999857/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((378549/125000 : ℚ) : ℝ) ≤ Real.log ((427 : ℕ)) / 2 := by
    have h := (log_br_427).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((427 : ℕ)) / 2 ≤ ((60567841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_427).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 976463/1250000) (δ := 271/31250000) (ψ := -65899/100000) 339 163
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t427 : ((-241944497069/5000000000000 : ℚ) : ℝ) ≤ stT339o2 427 := by
  have hc : ((-999907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((427 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-241944497069/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-999907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c428 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-37153/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60591231/20000000 : ℚ) : ℝ) ≤ Real.log ((428 : ℕ)) / 2 := by
    have h := (log_br_428).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((428 : ℕ)) / 2 ≤ ((473369/156250 : ℚ) : ℝ) := by
    have h := (log_br_428).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3452533/5000000) (δ := 8529/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t428 : ((-3591915039/80000000000 : ℚ) : ℝ) ≤ stT339o2 428 := by
  have hc : ((-7431/8000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((428 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3591915039/80000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-7431/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c429 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-714319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60614569/20000000 : ℚ) : ℝ) ≤ Real.log ((429 : ℕ)) / 2 := by
    have h := (log_br_429).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((429 : ℕ)) / 2 ≤ ((6061457/2000000 : ℚ) : ℝ) := by
    have h := (log_br_429).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2958059/5000000) (δ := 8629/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t429 : ((-68980185009/2000000000000 : ℚ) : ℝ) ≤ stT339o2 429 := by
  have hc : ((-714369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((429 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68980185009/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-714369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c430 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-390343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15159463/5000000 : ℚ) : ℝ) ≤ Real.log ((430 : ℕ)) / 2 := by
    have h := (log_br_430).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((430 : ℕ)) / 2 ≤ ((60637853/20000000 : ℚ) : ℝ) := by
    have h := (log_br_430).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4929501/10000000) (δ := 8579/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t430 : ((-188264291499/10000000000000 : ℚ) : ℝ) ≤ stT339o2 430 := by
  have hc : ((-390393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((430 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188264291499/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-390393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c431 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-729/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1516527/500000 : ℚ) : ℝ) ≤ Real.log ((431 : ℕ)) / 2 := by
    have h := (log_br_431).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((431 : ℕ)) / 2 ≤ ((60661081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_431).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -789043/2000000) (δ := 4287/500000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t431 : ((-44194507/125000000000 : ℚ) : ℝ) ≤ stT339o2 431 := by
  have hc : ((-367/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((431 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44194507/125000000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-367/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c432 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((376047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12136851/4000000 : ℚ) : ℝ) ≤ Real.log ((432 : ℕ)) / 2 := by
    have h := (log_br_432).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((432 : ℕ)) / 2 ≤ ((1896383/625000 : ℚ) : ℝ) := by
    have h := (log_br_432).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1481587/5000000) (δ := 8529/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t432 : ((1447212453/80000000000 : ℚ) : ℝ) ≤ stT339o2 432 := by
  have hc : ((375997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((432 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1447212453/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((375997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c433 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((701461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60707377/20000000 : ℚ) : ℝ) ≤ Real.log ((433 : ℕ)) / 2 := by
    have h := (log_br_433).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((433 : ℕ)) / 2 ≤ ((30353689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_433).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1983379/10000000) (δ := 8629/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t433 : ((337076382859/10000000000000 : ℚ) : ℝ) ≤ stT339o2 433 := by
  have hc : ((701411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((433 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337076382859/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((701411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c434 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((57509/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12146089/4000000 : ℚ) : ℝ) ≤ Real.log ((434 : ℕ)) / 2 := by
    have h := (log_br_434).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((434 : ℕ)) / 2 ≤ ((30365223/10000000 : ℚ) : ℝ) := by
    have h := (log_br_434).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1005873/10000000) (δ := 2131/250000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t434 : ((44165892141/1000000000000 : ℚ) : ℝ) ≤ stT339o2 434 := by
  have hc : ((460047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((434 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44165892141/1000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((460047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c435 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((39997/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3037673/1000000 : ℚ) : ℝ) ≤ Real.log ((435 : ℕ)) / 2 := by
    have h := (log_br_435).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((435 : ℕ)) / 2 ≤ ((60753461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_435).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7653/2500000) (δ := 8579/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t435 : ((3835224537/80000000000 : ℚ) : ℝ) ≤ stT339o2 435 := by
  have hc : ((7999/8000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((435 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3835224537/80000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((7999/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c436 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((232447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30388211/10000000 : ℚ) : ℝ) ≤ Real.log ((436 : ℕ)) / 2 := by
    have h := (log_br_436).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((436 : ℕ)) / 2 ≤ ((60776423/20000000 : ℚ) : ℝ) := by
    have h := (log_br_436).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 471201/5000000) (δ := 4337/500000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t436 : ((222631807397/5000000000000 : ℚ) : ℝ) ≤ stT339o2 436 := by
  have hc : ((464869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((436 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222631807397/5000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((464869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c437 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((180299/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60799331/20000000 : ℚ) : ℝ) ≤ Real.log ((437 : ℕ)) / 2 := by
    have h := (log_br_437).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((437 : ℕ)) / 2 ≤ ((15199833/5000000 : ℚ) : ℝ) := by
    have h := (log_br_437).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1913171/10000000) (δ := 539/62500000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t437 : ((43121285643/1250000000000 : ℚ) : ℝ) ≤ stT339o2 437 := by
  have hc : ((360573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((437 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43121285643/1250000000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((360573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c438 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((406011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60822189/20000000 : ℚ) : ℝ) ≤ Real.log ((438 : ℕ)) / 2 := by
    have h := (log_br_438).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((438 : ℕ)) / 2 ≤ ((6082219/2000000 : ℚ) : ℝ) := by
    have h := (log_br_438).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2881779/10000000) (δ := 2131/250000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t438 : ((96987736549/5000000000000 : ℚ) : ℝ) ≤ stT339o2 438 := by
  have hc : ((405961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((438 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96987736549/5000000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((405961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c439 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((6307/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30422497/10000000 : ℚ) : ℝ) ≤ Real.log ((439 : ℕ)) / 2 := by
    have h := (log_br_439).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((439 : ℕ)) / 2 ≤ ((12168999/4000000 : ℚ) : ℝ) := by
    have h := (log_br_439).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3848141/10000000) (δ := 8479/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t439 : ((3005388081/2000000000000 : ℚ) : ℝ) ≤ stT339o2 439 := by
  have hc : ((6297/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((439 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3005388081/2000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((6297/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c440 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-21673/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60867747/20000000 : ℚ) : ℝ) ≤ Real.log ((440 : ℕ)) / 2 := by
    have h := (log_br_440).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((440 : ℕ)) / 2 ≤ ((15216937/5000000 : ℚ) : ℝ) := by
    have h := (log_br_440).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4812299/10000000) (δ := 539/62500000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t440 : ((-20667404847/1250000000000 : ℚ) : ℝ) ≤ stT339o2 440 := by
  have hc : ((-173409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((440 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20667404847/1250000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-173409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c441 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-673479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/1250000 : ℚ) : ℝ) ≤ Real.log ((441 : ℕ)) / 2 := by
    have h := (log_br_441).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((441 : ℕ)) / 2 ≤ ((60890449/20000000 : ℚ) : ℝ) := by
    have h := (log_br_441).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2887127/5000000) (δ := 4287/500000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t441 : ((-320728448039/10000000000000 : ℚ) : ℝ) ≤ stT339o2 441 := by
  have hc : ((-673529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((441 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320728448039/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-673529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c442 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-901327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30456549/10000000 : ℚ) : ℝ) ≤ Real.log ((442 : ℕ)) / 2 := by
    have h := (log_br_442).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((442 : ℕ)) / 2 ≤ ((60913099/20000000 : ℚ) : ℝ) := by
    have h := (log_br_442).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 210439/312500) (δ := 8479/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t442 : ((-107185443201/2500000000000 : ℚ) : ℝ) ≤ stT339o2 442 := by
  have hc : ((-901377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((442 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107185443201/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-901377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c443 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-997893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((60935697/20000000 : ℚ) : ℝ) ≤ Real.log ((443 : ℕ)) / 2 := by
    have h := (log_br_443).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((443 : ℕ)) / 2 ≤ ((30467849/10000000 : ℚ) : ℝ) := by
    have h := (log_br_443).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7691681/10000000) (δ := 8629/1000000000) (ψ := -65899/100000) 339 164
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t443 : ((-94827537689/2000000000000 : ℚ) : ℝ) ≤ stT339o2 443 := by
  have hc : ((-997943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((443 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94827537689/2000000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-997943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c444 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-950091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12191649/4000000 : ℚ) : ℝ) ≤ Real.log ((444 : ℕ)) / 2 := by
    have h := (log_br_444).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((444 : ℕ)) / 2 ≤ ((30479123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_444).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7060811/10000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t444 : ((-450916965639/10000000000000 : ℚ) : ℝ) ≤ stT339o2 444 := by
  have hc : ((-950141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((444 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450916965639/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-950141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c445 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-191437/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30490371/10000000 : ℚ) : ℝ) ≤ Real.log ((445 : ℕ)) / 2 := by
    have h := (log_br_445).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((445 : ℕ)) / 2 ≤ ((60980743/20000000 : ℚ) : ℝ) := by
    have h := (log_br_445).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6107501/10000000) (δ := 8567/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t445 : ((-90755869677/2500000000000 : ℚ) : ℝ) ≤ stT339o2 445 := by
  have hc : ((-382899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((445 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90755869677/2500000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-382899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c446 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-472149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61003189/20000000 : ℚ) : ℝ) ≤ Real.log ((446 : ℕ)) / 2 := by
    have h := (log_br_446).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((446 : ℕ)) / 2 ≤ ((6100319/2000000 : ℚ) : ℝ) := by
    have h := (log_br_446).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5156309/10000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t446 : ((-111796418643/5000000000000 : ℚ) : ℝ) ≤ stT339o2 446 := by
  have hc : ((-472199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((446 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111796418643/5000000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-472199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c447 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-111881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12205117/4000000 : ℚ) : ℝ) ≤ Real.log ((447 : ℕ)) / 2 := by
    have h := (log_br_447).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((447 : ℕ)) / 2 ≤ ((30512793/10000000 : ℚ) : ℝ) := by
    have h := (log_br_447).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4207279/10000000) (δ := 8617/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t447 : ((-6617696513/1250000000000 : ℚ) : ℝ) ≤ stT339o2 447 := by
  have hc : ((-111931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((447 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6617696513/1250000000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-111931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c448 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((263517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15261983/5000000 : ℚ) : ℝ) ≤ Real.log ((448 : ℕ)) / 2 := by
    have h := (log_br_448).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((448 : ℕ)) / 2 ≤ ((61047933/20000000 : ℚ) : ℝ) := by
    have h := (log_br_448).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -130413/400000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t448 : ((24895260297/2000000000000 : ℚ) : ℝ) ≤ stT339o2 448 := by
  have hc : ((263467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((448 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24895260297/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((263467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c449 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((300433/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15267557/5000000 : ℚ) : ℝ) ≤ Real.log ((449 : ℕ)) / 2 := by
    have h := (log_br_449).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((449 : ℕ)) / 2 ≤ ((61070229/20000000 : ℚ) : ℝ) := by
    have h := (log_br_449).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -578883/2500000) (δ := 8667/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t449 : ((17721405879/625000000000 : ℚ) : ℝ) ≤ stT339o2 449 := by
  have hc : ((37551/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((449 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17721405879/625000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((37551/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c450 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((852981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2443699/800000 : ℚ) : ℝ) ≤ Real.log ((450 : ℕ)) / 2 := by
    have h := (log_br_450).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((450 : ℕ)) / 2 ≤ ((15273119/5000000 : ℚ) : ℝ) := by
    have h := (log_br_450).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -274563/2000000) (δ := 8517/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t450 : ((100518771281/2500000000000 : ℚ) : ℝ) ≤ stT339o2 450 := by
  have hc : ((852931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((450 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100518771281/2500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((852931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c451 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((197019/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61114673/20000000 : ℚ) : ℝ) ≤ Real.log ((451 : ℕ)) / 2 := by
    have h := (log_br_451).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((451 : ℕ)) / 2 ≤ ((30557337/10000000 : ℚ) : ℝ) := by
    have h := (log_br_451).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -17287/400000) (δ := 8617/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t451 : ((92767794929/2000000000000 : ℚ) : ℝ) ≤ stT339o2 451 := by
  have hc : ((197009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((451 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92767794929/2000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((197009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c452 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((979559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61136821/20000000 : ℚ) : ℝ) ≤ Real.log ((452 : ℕ)) / 2 := by
    have h := (log_br_452).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((452 : ℕ)) / 2 ≤ ((30568411/10000000 : ℚ) : ℝ) := by
    have h := (log_br_452).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 506347/10000000) (δ := 1067/125000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t452 : ((11518046331/250000000000 : ℚ) : ℝ) ≤ stT339o2 452 := by
  have hc : ((979509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((452 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11518046331/250000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((979509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c453 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((83803/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61158921/20000000 : ℚ) : ℝ) ≤ Real.log ((453 : ℕ)) / 2 := by
    have h := (log_br_453).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((453 : ℕ)) / 2 ≤ ((30579461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_453).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 721417/5000000) (δ := 8617/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t453 : ((246072827/6250000000 : ℚ) : ℝ) ≤ stT339o2 453 := by
  have hc : ((41899/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((453 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).1
  have hw2 : ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5873/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246072827/6250000000 : ℚ) : ℝ)
      = ((5873/125000 : ℚ) : ℝ) * ((41899/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c454 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((290483/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61180971/20000000 : ℚ) : ℝ) ≤ Real.log ((454 : ℕ)) / 2 := by
    have h := (log_br_454).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((454 : ℕ)) / 2 ≤ ((15295243/5000000 : ℚ) : ℝ) := by
    have h := (log_br_454).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2377203/10000000) (δ := 8517/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t454 : ((68159309967/2500000000000 : ℚ) : ℝ) ≤ stT339o2 454 := by
  have hc : ((145229/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((454 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).1
  have hw2 : ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((469323/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68159309967/2500000000000 : ℚ) : ℝ)
      = ((469323/10000000 : ℚ) : ℝ) * ((145229/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c455 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((122231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30601487/10000000 : ℚ) : ℝ) ≤ Real.log ((455 : ℕ)) / 2 := by
    have h := (log_br_455).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((455 : ℕ)) / 2 ≤ ((2448119/800000 : ℚ) : ℝ) := by
    have h := (log_br_455).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 165479/500000) (δ := 8567/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t455 : ((28645514121/2500000000000 : ℚ) : ℝ) ≤ stT339o2 455 := by
  have hc : ((61103/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((455 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28645514121/2500000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((61103/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c456 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-12483/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1913279/625000 : ℚ) : ℝ) ≤ Real.log ((456 : ℕ)) / 2 := by
    have h := (log_br_456).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((456 : ℕ)) / 2 ≤ ((61224929/20000000 : ℚ) : ℝ) := by
    have h := (log_br_456).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4239881/10000000) (δ := 4243/500000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t456 : ((-731005373/125000000000 : ℚ) : ℝ) ≤ stT339o2 456 := by
  have hc : ((-1561/12500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((456 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731005373/125000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-1561/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c457 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-476303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61246833/20000000 : ℚ) : ℝ) ≤ Real.log ((457 : ℕ)) / 2 := by
    have h := (log_br_457).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((457 : ℕ)) / 2 ≤ ((30623417/10000000 : ℚ) : ℝ) := by
    have h := (log_br_457).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1033621/2000000) (δ := 8617/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t457 : ((-222828882693/10000000000000 : ℚ) : ℝ) ≤ stT339o2 457 := by
  have hc : ((-476353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((457 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222828882693/10000000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-476353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c458 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-762351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61268691/20000000 : ℚ) : ℝ) ≤ Real.log ((458 : ℕ)) / 2 := by
    have h := (log_br_458).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((458 : ℕ)) / 2 ≤ ((15317173/5000000 : ℚ) : ℝ) := by
    have h := (log_br_458).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3047169/5000000) (δ := 8517/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t458 : ((-35624711527/1000000000000 : ℚ) : ℝ) ≤ stT339o2 458 := by
  have hc : ((-762401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((458 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35624711527/1000000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-762401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c459 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-472343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30645251/10000000 : ℚ) : ℝ) ≤ Real.log ((459 : ℕ)) / 2 := by
    have h := (log_br_459).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((459 : ℕ)) / 2 ≤ ((61290503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_459).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7018579/10000000) (δ := 8567/1000000000) (ψ := -65899/100000) 339 165
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t459 : ((-13780185003/312500000000 : ℚ) : ℝ) ≤ stT339o2 459 := by
  have hc : ((-29523/31250 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((459 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).2
  have h0 : (0:ℝ) ≤ ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13780185003/312500000000 : ℚ) : ℝ)
      = ((466761/10000000 : ℚ) : ℝ) * ((-29523/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c460 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-499699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7664033/2500000 : ℚ) : ℝ) ≤ Real.log ((460 : ℕ)) / 2 := by
    have h := (log_br_460).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((460 : ℕ)) / 2 ≤ ((12262453/4000000 : ℚ) : ℝ) := by
    have h := (log_br_460).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7767219/10000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t460 : ((-58249453543/1250000000000 : ℚ) : ℝ) ≤ stT339o2 460 := by
  have hc : ((-124931/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((460 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).2
  have h0 : (0:ℝ) ≤ ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58249453543/1250000000000 : ℚ) : ℝ)
      = ((466253/10000000 : ℚ) : ℝ) * ((-124931/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c461 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-919971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3066699/1000000 : ℚ) : ℝ) ≤ Real.log ((461 : ℕ)) / 2 := by
    have h := (log_br_461).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((461 : ℕ)) / 2 ≤ ((61333981/20000000 : ℚ) : ℝ) := by
    have h := (log_br_461).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1711751/2500000) (δ := 107/12500000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t461 : ((-428497020687/10000000000000 : ℚ) : ℝ) ≤ stT339o2 461 := by
  have hc : ((-920021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((461 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428497020687/10000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-920021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c462 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-358933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((479341/156250 : ℚ) : ℝ) ≤ Real.log ((462 : ℕ)) / 2 := by
    have h := (log_br_462).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((462 : ℕ)) / 2 ≤ ((61355649/20000000 : ℚ) : ℝ) := by
    have h := (log_br_462).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2964411/5000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t462 : ((-83501348397/2500000000000 : ℚ) : ℝ) ≤ stT339o2 462 := by
  have hc : ((-179479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((462 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83501348397/2500000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-179479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c463 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-420721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6137727/2000000 : ℚ) : ℝ) ≤ Real.log ((463 : ℕ)) / 2 := by
    have h := (log_br_463).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((463 : ℕ)) / 2 ≤ ((61377271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_463).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -501259/1000000) (δ := 8493/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t463 : ((-9777455727/500000000000 : ℚ) : ℝ) ≤ stT339o2 463 := by
  have hc : ((-420771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((463 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9777455727/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-420771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c464 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-6849/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12279769/4000000 : ℚ) : ℝ) ≤ Real.log ((464 : ℕ)) / 2 := by
    have h := (log_br_464).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((464 : ℕ)) / 2 ≤ ((30699423/10000000 : ℚ) : ℝ) := by
    have h := (log_br_464).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4098349/10000000) (δ := 8643/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t464 : ((-1590947053/500000000000 : ℚ) : ℝ) ≤ stT339o2 464 := by
  have hc : ((-3427/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((464 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1590947053/500000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-3427/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c465 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((292053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30710187/10000000 : ℚ) : ℝ) ≤ Real.log ((465 : ℕ)) / 2 := by
    have h := (log_br_465).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((465 : ℕ)) / 2 ≤ ((491363/160000 : ℚ) : ℝ) := by
    have h := (log_br_465).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1593029/5000000) (δ := 8493/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t465 : ((67706443607/5000000000000 : ℚ) : ℝ) ≤ stT339o2 465 := by
  have hc : ((292003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((465 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67706443607/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((292003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c466 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((306753/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((960029/312500 : ℚ) : ℝ) ≤ Real.log ((466 : ℕ)) / 2 := by
    have h := (log_br_466).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((466 : ℕ)) / 2 ≤ ((61441857/20000000 : ℚ) : ℝ) := by
    have h := (log_br_466).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1137879/5000000) (δ := 8593/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t466 : ((17761123181/625000000000 : ℚ) : ℝ) ≤ stT339o2 466 := by
  have hc : ((38341/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((466 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17761123181/625000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((38341/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c467 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((213527/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15365823/5000000 : ℚ) : ℝ) ≤ Real.log ((467 : ℕ)) / 2 := by
    have h := (log_br_467).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((467 : ℕ)) / 2 ≤ ((61463293/20000000 : ℚ) : ℝ) := by
    have h := (log_br_467).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -85463/625000) (δ := 107/12500000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t467 : ((24700638447/625000000000 : ℚ) : ℝ) ≤ stT339o2 467 := by
  have hc : ((427029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((467 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24700638447/625000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((427029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c468 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((491523/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30742341/10000000 : ℚ) : ℝ) ≤ Real.log ((468 : ℕ)) / 2 := by
    have h := (log_br_468).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((468 : ℕ)) / 2 ≤ ((61484683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_468).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -461007/10000000) (δ := 433/50000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t468 : ((454389901/10000000000 : ℚ) : ℝ) ≤ stT339o2 468 := by
  have hc : ((245749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((468 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454389901/10000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((245749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c469 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((984307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61506027/20000000 : ℚ) : ℝ) ≤ Real.log ((469 : ℕ)) / 2 := by
    have h := (log_br_469).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((469 : ℕ)) / 2 ≤ ((15376507/5000000 : ℚ) : ℝ) := by
    have h := (log_br_469).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 13859/312500) (δ := 8543/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t469 : ((454487559549/10000000000000 : ℚ) : ℝ) ≤ stT339o2 469 := by
  have hc : ((984257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((469 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454487559549/10000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((984257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c470 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((858523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30763663/10000000 : ℚ) : ℝ) ≤ Real.log ((470 : ℕ)) / 2 := by
    have h := (log_br_470).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((470 : ℕ)) / 2 ≤ ((61527327/20000000 : ℚ) : ℝ) := by
    have h := (log_br_470).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1346033/10000000) (δ := 8493/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t470 : ((79196709669/2000000000000 : ℚ) : ℝ) ≤ stT339o2 470 := by
  have hc : ((858473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((470 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79196709669/2000000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((858473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c471 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((155663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3077429/1000000 : ℚ) : ℝ) ≤ Real.log ((471 : ℕ)) / 2 := by
    have h := (log_br_471).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((471 : ℕ)) / 2 ≤ ((61548581/20000000 : ℚ) : ℝ) := by
    have h := (log_br_471).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2246671/10000000) (δ := 107/12500000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t471 : ((5737588731/200000000000 : ℚ) : ℝ) ≤ stT339o2 471 := by
  have hc : ((311301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((471 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5737588731/200000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((311301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c472 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((307567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61569789/20000000 : ℚ) : ℝ) ≤ Real.log ((472 : ℕ)) / 2 := by
    have h := (log_br_472).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((472 : ℕ)) / 2 ≤ ((6156979/2000000 : ℚ) : ℝ) := by
    have h := (log_br_472).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3145403/10000000) (δ := 8643/1000000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t472 : ((141546077379/10000000000000 : ℚ) : ℝ) ≤ stT339o2 472 := by
  have hc : ((307517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((472 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141546077379/10000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((307517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c473 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-23039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61590953/20000000 : ℚ) : ℝ) ≤ Real.log ((473 : ℕ)) / 2 := by
    have h := (log_br_473).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((473 : ℕ)) / 2 ≤ ((30795477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_473).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4042227/10000000) (δ := 851/100000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t473 : ((-1325606283/625000000000 : ℚ) : ℝ) ≤ stT339o2 473 := by
  have hc : ((-2883/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((473 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1325606283/625000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-2883/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c474 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-98293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61612073/20000000 : ℚ) : ℝ) ≤ Real.log ((474 : ℕ)) / 2 := by
    have h := (log_br_474).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((474 : ℕ)) / 2 ≤ ((30806037/10000000 : ℚ) : ℝ) := by
    have h := (log_br_474).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4937187/10000000) (δ := 851/100000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t474 : ((-22576644519/1250000000000 : ℚ) : ℝ) ≤ stT339o2 474 := by
  have hc : ((-196611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((474 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22576644519/1250000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-196611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c475 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-689863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15408287/5000000 : ℚ) : ℝ) ≤ Real.log ((475 : ℕ)) / 2 := by
    have h := (log_br_475).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((475 : ℕ)) / 2 ≤ ((61633149/20000000 : ℚ) : ℝ) := by
    have h := (log_br_475).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 36439/62500) (δ := 107/12500000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t475 : ((-19784635101/625000000000 : ℚ) : ℝ) ≤ stT339o2 475 := by
  have hc : ((-689913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((475 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19784635101/625000000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-689913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c476 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-899121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30827089/10000000 : ℚ) : ℝ) ≤ Real.log ((476 : ℕ)) / 2 := by
    have h := (log_br_476).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((476 : ℕ)) / 2 ≤ ((61654179/20000000 : ℚ) : ℝ) := by
    have h := (log_br_476).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3360693/5000000) (δ := 433/50000000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t476 : ((-8242700557/200000000000 : ℚ) : ℝ) ≤ stT339o2 476 := by
  have hc : ((-899171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((476 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8242700557/200000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-899171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c477 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-248817/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15418791/5000000 : ℚ) : ℝ) ≤ Real.log ((477 : ℕ)) / 2 := by
    have h := (log_br_477).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((477 : ℕ)) / 2 ≤ ((12335033/4000000 : ℚ) : ℝ) := by
    have h := (log_br_477).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1902667/2500000) (δ := 107/12500000) (ψ := -65899/100000) 339 166
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t477 : ((-227862628671/5000000000000 : ℚ) : ℝ) ≤ stT339o2 477 := by
  have hc : ((-497659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((477 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227862628671/5000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-497659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c478 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-966989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61696107/20000000 : ℚ) : ℝ) ≤ Real.log ((478 : ℕ)) / 2 := by
    have h := (log_br_478).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((478 : ℕ)) / 2 ≤ ((15424027/5000000 : ℚ) : ℝ) := by
    have h := (log_br_478).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1441967/2000000) (δ := 173/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t478 : ((-44231396821/1000000000000 : ℚ) : ℝ) ≤ stT339o2 478 := by
  have hc : ((-967039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((478 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44231396821/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-967039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c479 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-81857/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12343401/4000000 : ℚ) : ℝ) ≤ Real.log ((479 : ℕ)) / 2 := by
    have h := (log_br_479).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((479 : ℕ)) / 2 ≤ ((30858503/10000000 : ℚ) : ℝ) := by
    have h := (log_br_479).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6324283/10000000) (δ := 8603/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t479 : ((-1168866567/31250000000 : ℚ) : ℝ) ≤ stT339o2 479 := by
  have hc : ((-40931/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((479 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1168866567/31250000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-40931/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c480 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-569097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61737861/20000000 : ℚ) : ℝ) ≤ Real.log ((480 : ℕ)) / 2 := by
    have h := (log_br_480).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((480 : ℕ)) / 2 ≤ ((30868931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_480).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -544051/1000000) (δ := 8603/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t480 : ((-64944795023/2500000000000 : ℚ) : ℝ) ≤ stT339o2 480 := by
  have hc : ((-569147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((480 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64944795023/2500000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-569147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c481 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-124991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3859917/1250000 : ℚ) : ℝ) ≤ Real.log ((481 : ℕ)) / 2 := by
    have h := (log_br_481).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((481 : ℕ)) / 2 ≤ ((61758673/20000000 : ℚ) : ℝ) := by
    have h := (log_br_481).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1139661/2500000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t481 : ((-7125302547/625000000000 : ℚ) : ℝ) ≤ stT339o2 481 := by
  have hc : ((-15627/62500 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((481 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7125302547/625000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-15627/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c482 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((9921/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61779441/20000000 : ℚ) : ℝ) ≤ Real.log ((482 : ℕ)) / 2 := by
    have h := (log_br_482).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((482 : ℕ)) / 2 ≤ ((30889721/10000000 : ℚ) : ℝ) := by
    have h := (log_br_482).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3678557/10000000) (δ := 171/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t482 : ((1129152273/250000000000 : ℚ) : ℝ) ≤ stT339o2 482 := by
  have hc : ((2479/25000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((482 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1129152273/250000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((2479/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c483 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((217781/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30900083/10000000 : ℚ) : ℝ) ≤ Real.log ((483 : ℕ)) / 2 := by
    have h := (log_br_483).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((483 : ℕ)) / 2 ≤ ((61800167/20000000 : ℚ) : ℝ) := by
    have h := (log_br_483).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -560067/2000000) (δ := 43/5000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t483 : ((4954112317/250000000000 : ℚ) : ℝ) ≤ stT339o2 483 := by
  have hc : ((54439/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((483 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4954112317/250000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((54439/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c484 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((718219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61820849/20000000 : ℚ) : ℝ) ≤ Real.log ((484 : ℕ)) / 2 := by
    have h := (log_br_484).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((484 : ℕ)) / 2 ≤ ((1236417/400000 : ℚ) : ℝ) := by
    have h := (log_br_484).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1923893/10000000) (δ := 171/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t484 : ((65288025621/2000000000000 : ℚ) : ℝ) ≤ stT339o2 484 := by
  have hc : ((718169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((484 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65288025621/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((718169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c485 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((2283/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3865093/1250000 : ℚ) : ℝ) ≤ Real.log ((485 : ℕ)) / 2 := by
    have h := (log_br_485).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((485 : ℕ)) / 2 ≤ ((61841489/20000000 : ℚ) : ℝ) := by
    have h := (log_br_485).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -262329/2500000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t485 : ((2073197497/50000000000 : ℚ) : ℝ) ≤ stT339o2 485 := by
  have hc : ((18263/20000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((485 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2073197497/50000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((18263/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c486 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((99751/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30931043/10000000 : ℚ) : ℝ) ≤ Real.log ((486 : ℕ)) / 2 := by
    have h := (log_br_486).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((486 : ℕ)) / 2 ≤ ((61862087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_486).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7059/400000) (δ := 43/5000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t486 : ((22622841657/500000000000 : ℚ) : ℝ) ≤ stT339o2 486 := by
  have hc : ((49873/50000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((486 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22622841657/500000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((49873/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c487 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((120207/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61882641/20000000 : ℚ) : ℝ) ≤ Real.log ((487 : ℕ)) / 2 := by
    have h := (log_br_487).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((487 : ℕ)) / 2 ≤ ((30941321/10000000 : ℚ) : ℝ) := by
    have h := (log_br_487).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 694543/10000000) (δ := 171/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t487 : ((217872513829/5000000000000 : ℚ) : ℝ) ≤ stT339o2 487 := by
  have hc : ((480803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((487 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217872513829/5000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((480803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c488 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((810663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((30951577/10000000 : ℚ) : ℝ) ≤ Real.log ((488 : ℕ)) / 2 := by
    have h := (log_br_488).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((488 : ℕ)) / 2 ≤ ((12380631/4000000 : ℚ) : ℝ) := by
    have h := (log_br_488).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1563781/10000000) (δ := 8553/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t488 : ((183473335807/5000000000000 : ℚ) : ℝ) ≤ stT339o2 488 := by
  have hc : ((810613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((488 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183473335807/5000000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((810613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c489 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((563253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7740453/2500000 : ℚ) : ℝ) ≤ Real.log ((489 : ℕ)) / 2 := by
    have h := (log_br_489).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((489 : ℕ)) / 2 ≤ ((495389/160000 : ℚ) : ℝ) := by
    have h := (log_br_489).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2431197/10000000) (δ := 8653/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t489 : ((50937768929/2000000000000 : ℚ) : ℝ) ≤ stT339o2 489 := by
  have hc : ((563203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((489 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50937768929/2000000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((563203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c490 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((124693/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61944053/20000000 : ℚ) : ℝ) ≤ Real.log ((490 : ℕ)) / 2 := by
    have h := (log_br_490).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((490 : ℕ)) / 2 ≤ ((30972027/10000000 : ℚ) : ℝ) := by
    have h := (log_br_490).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 824219/2500000) (δ := 8603/1000000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t490 : ((14079785751/1250000000000 : ℚ) : ℝ) ≤ stT339o2 490 := by
  have hc : ((31167/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((490 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14079785751/1250000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((31167/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c491 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-18679/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61964441/20000000 : ℚ) : ℝ) ≤ Real.log ((491 : ℕ)) / 2 := by
    have h := (log_br_491).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((491 : ℕ)) / 2 ≤ ((30982221/10000000 : ℚ) : ℝ) := by
    have h := (log_br_491).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2080409/5000000) (δ := 171/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t491 : ((-4217116783/1000000000000 : ℚ) : ℝ) ≤ stT339o2 491 := by
  have hc : ((-18689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((491 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4217116783/1000000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-18689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c492 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-424487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((61984787/20000000 : ℚ) : ℝ) ≤ Real.log ((492 : ℕ)) / 2 := by
    have h := (log_br_492).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((492 : ℕ)) / 2 ≤ ((15496197/5000000 : ℚ) : ℝ) := by
    have h := (log_br_492).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 251149/500000) (δ := 173/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t492 : ((-38279227679/2000000000000 : ℚ) : ℝ) ≤ stT339o2 492 := by
  have hc : ((-424537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((492 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38279227679/2000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-424537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c493 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-705089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62005091/20000000 : ℚ) : ℝ) ≤ Real.log ((493 : ℕ)) / 2 := by
    have h := (log_br_493).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((493 : ℕ)) / 2 ≤ ((15501273/5000000 : ℚ) : ℝ) := by
    have h := (log_br_493).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2941681/5000000) (δ := 173/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t493 : ((-158789546271/5000000000000 : ℚ) : ℝ) ≤ stT339o2 493 := by
  have hc : ((-705139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((493 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158789546271/5000000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-705139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c494 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-225677/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12405071/4000000 : ℚ) : ℝ) ≤ Real.log ((494 : ℕ)) / 2 := by
    have h := (log_br_494).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((494 : ℕ)) / 2 ≤ ((15506339/5000000 : ℚ) : ℝ) := by
    have h := (log_br_494).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6742049/10000000) (δ := 173/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t494 : ((-101542671219/2500000000000 : ℚ) : ℝ) ≤ stT339o2 494 := by
  have hc : ((-451379/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((494 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101542671219/2500000000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-451379/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c495 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-994801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62045577/20000000 : ℚ) : ℝ) ≤ Real.log ((495 : ℕ)) / 2 := by
    have h := (log_br_495).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((495 : ℕ)) / 2 ≤ ((31022789/10000000 : ℚ) : ℝ) := by
    have h := (log_br_495).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1899739/2500000) (δ := 171/20000000) (ψ := -65899/100000) 339 167
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t495 : ((-447152694417/10000000000000 : ℚ) : ℝ) ≤ stT339o2 495 := by
  have hc : ((-994851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((495 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-447152694417/10000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-994851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c496 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-24283/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((62065759/20000000 : ℚ) : ℝ) ≤ Real.log ((496 : ℕ)) / 2 := by
    have h := (log_br_496).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((496 : ℕ)) / 2 ≤ ((387911/125000 : ℚ) : ℝ) := by
    have h := (log_br_496).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1450759/2000000) (δ := 4279/500000000) (ψ := -65899/100000) 339 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t496 : ((-21807936459/500000000000 : ℚ) : ℝ) ≤ stT339o2 496 := by
  have hc : ((-97137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((496 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21807936459/500000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-97137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c497 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-835659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((620859/200000 : ℚ) : ℝ) ≤ Real.log ((497 : ℕ)) / 2 := by
    have h := (log_br_497).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((497 : ℕ)) / 2 ≤ ((62085901/20000000 : ℚ) : ℝ) := by
    have h := (log_br_497).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -20001/31250) (δ := 269/31250000) (ψ := -65899/100000) 339 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t497 : ((-187433650229/5000000000000 : ℚ) : ℝ) ≤ stT339o2 497 := by
  have hc : ((-835709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((497 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187433650229/5000000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-835709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c498 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-604101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((31053/10000 : ℚ) : ℝ) ≤ Real.log ((498 : ℕ)) / 2 := by
    have h := (log_br_498).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((498 : ℕ)) / 2 ≤ ((62106001/20000000 : ℚ) : ℝ) := by
    have h := (log_br_498).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5548583/10000000) (δ := 1709/200000000) (ψ := -65899/100000) 339 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t498 : ((-270726708761/10000000000000 : ℚ) : ℝ) ≤ stT339o2 498 := by
  have hc : ((-604151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((498 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270726708761/10000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-604151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c499 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-4746/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3106303/1000000 : ℚ) : ℝ) ≤ Real.log ((499 : ℕ)) / 2 := by
    have h := (log_br_499).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((499 : ℕ)) / 2 ≤ ((62126061/20000000 : ℚ) : ℝ) := by
    have h := (log_br_499).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -234927/500000) (δ := 269/31250000) (ψ := -65899/100000) 339 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t499 : ((-33999257407/2500000000000 : ℚ) : ℝ) ≤ stT339o2 499 := by
  have hc : ((-151897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((499 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33999257407/2500000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-151897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_c500 :
    |Real.cos (((339 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((15357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3850193/10000000) (δ := 1709/200000000) (ψ := -65899/100000) 339 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st339o2_t500 : ((1714167429/1250000000000 : ℚ) : ℝ) ≤ stT339o2 500 := by
  have hc : ((3833/125000 : ℚ) : ℝ)
      ≤ Real.cos (((339 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st339o2_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).1
  have hw2 : ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((447213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1714167429/1250000000000 : ℚ) : ℝ)
      = ((447213/10000000 : ℚ) : ℝ) * ((3833/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st339o2_p1 : ((790561/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT339o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st339o2_t1

theorem st339o2_p2 : ((409923108817/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT339o2 (i+1)) + stT339o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 1
    simpa using h
  have hprev := st339o2_p1
  have hstep := st339o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p3 : ((9953490503353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT339o2 (i+1)) + stT339o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 2
    simpa using h
  have hprev := st339o2_p2
  have hstep := st339o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p4 : ((2476957251719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT339o2 (i+1)) + stT339o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 3
    simpa using h
  have hprev := st339o2_p3
  have hstep := st339o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p5 : ((52541313439/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT339o2 (i+1)) + stT339o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 4
    simpa using h
  have hprev := st339o2_p4
  have hstep := st339o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p6 : ((-204852514637/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT339o2 (i+1)) + stT339o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 5
    simpa using h
  have hprev := st339o2_p5
  have hstep := st339o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p7 : ((-6346224399987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT339o2 (i+1)) + stT339o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 6
    simpa using h
  have hprev := st339o2_p6
  have hstep := st339o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p8 : ((-1321310691621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT339o2 (i+1)) + stT339o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 7
    simpa using h
  have hprev := st339o2_p7
  have hstep := st339o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p9 : ((-192482247899/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT339o2 (i+1)) + stT339o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 8
    simpa using h
  have hprev := st339o2_p8
  have hstep := st339o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p10 : ((-7129792288753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT339o2 (i+1)) + stT339o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 9
    simpa using h
  have hprev := st339o2_p9
  have hstep := st339o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p11 : ((-633738742611/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT339o2 (i+1)) + stT339o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 10
    simpa using h
  have hprev := st339o2_p10
  have hstep := st339o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p12 : ((-4492127112143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT339o2 (i+1)) + stT339o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 11
    simpa using h
  have hprev := st339o2_p11
  have hstep := st339o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p13 : ((-5331272027701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT339o2 (i+1)) + stT339o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 12
    simpa using h
  have hprev := st339o2_p12
  have hstep := st339o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p14 : ((-6126978405739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT339o2 (i+1)) + stT339o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 13
    simpa using h
  have hprev := st339o2_p13
  have hstep := st339o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p15 : ((-4734184364863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT339o2 (i+1)) + stT339o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 14
    simpa using h
  have hprev := st339o2_p14
  have hstep := st339o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p16 : ((-2708534364863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT339o2 (i+1)) + stT339o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 15
    simpa using h
  have hprev := st339o2_p15
  have hstep := st339o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p17 : ((-1268222802739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT339o2 (i+1)) + stT339o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 16
    simpa using h
  have hprev := st339o2_p16
  have hstep := st339o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p18 : ((-1495861640363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT339o2 (i+1)) + stT339o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 17
    simpa using h
  have hprev := st339o2_p17
  have hstep := st339o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p19 : ((-2613270294949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT339o2 (i+1)) + stT339o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 18
    simpa using h
  have hprev := st339o2_p18
  have hstep := st339o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p20 : ((-816725166143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT339o2 (i+1)) + stT339o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 19
    simpa using h
  have hprev := st339o2_p19
  have hstep := st339o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p21 : ((-307860270713/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT339o2 (i+1)) + stT339o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 20
    simpa using h
  have hprev := st339o2_p20
  have hstep := st339o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p22 : ((-2603729799653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT339o2 (i+1)) + stT339o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 21
    simpa using h
  have hprev := st339o2_p21
  have hstep := st339o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p23 : ((-5970691479091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT339o2 (i+1)) + stT339o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 22
    simpa using h
  have hprev := st339o2_p22
  have hstep := st339o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p24 : ((-4893479613607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT339o2 (i+1)) + stT339o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 23
    simpa using h
  have hprev := st339o2_p23
  have hstep := st339o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p25 : ((-3035269613607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT339o2 (i+1)) + stT339o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 24
    simpa using h
  have hprev := st339o2_p24
  have hstep := st339o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p26 : ((-537198452137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT339o2 (i+1)) + stT339o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 25
    simpa using h
  have hprev := st339o2_p25
  have hstep := st339o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p27 : ((420211430363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT339o2 (i+1)) + stT339o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 26
    simpa using h
  have hprev := st339o2_p26
  have hstep := st339o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p28 : ((682452077961/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT339o2 (i+1)) + stT339o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 27
    simpa using h
  have hprev := st339o2_p27
  have hstep := st339o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p29 : ((4471379537189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT339o2 (i+1)) + stT339o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 28
    simpa using h
  have hprev := st339o2_p28
  have hstep := st339o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p30 : ((561885958143/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT339o2 (i+1)) + stT339o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 29
    simpa using h
  have hprev := st339o2_p29
  have hstep := st339o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p31 : ((1384220572177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT339o2 (i+1)) + stT339o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 30
    simpa using h
  have hprev := st339o2_p30
  have hstep := st339o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p32 : ((205077723983/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT339o2 (i+1)) + stT339o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 31
    simpa using h
  have hprev := st339o2_p31
  have hstep := st339o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p33 : ((1264734607811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT339o2 (i+1)) + stT339o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 32
    simpa using h
  have hprev := st339o2_p32
  have hstep := st339o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p34 : ((336784480519/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT339o2 (i+1)) + stT339o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 33
    simpa using h
  have hprev := st339o2_p33
  have hstep := st339o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p35 : ((1093811223113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT339o2 (i+1)) + stT339o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 34
    simpa using h
  have hprev := st339o2_p34
  have hstep := st339o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p36 : ((2326326557411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT339o2 (i+1)) + stT339o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 35
    simpa using h
  have hprev := st339o2_p35
  have hstep := st339o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p37 : ((1508316589171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT339o2 (i+1)) + stT339o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 36
    simpa using h
  have hprev := st339o2_p36
  have hstep := st339o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p38 : ((791845975787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT339o2 (i+1)) + stT339o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 37
    simpa using h
  have hprev := st339o2_p37
  have hstep := st339o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p39 : ((2320260394921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT339o2 (i+1)) + stT339o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 38
    simpa using h
  have hprev := st339o2_p38
  have hstep := st339o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p40 : ((1740219552771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT339o2 (i+1)) + stT339o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 39
    simpa using h
  have hprev := st339o2_p39
  have hstep := st339o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p41 : ((1569676201433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT339o2 (i+1)) + stT339o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 40
    simpa using h
  have hprev := st339o2_p40
  have hstep := st339o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p42 : ((4555821207107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT339o2 (i+1)) + stT339o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 41
    simpa using h
  have hprev := st339o2_p41
  have hstep := st339o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p43 : ((635086265931/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT339o2 (i+1)) + stT339o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 42
    simpa using h
  have hprev := st339o2_p42
  have hstep := st339o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p44 : ((745944396391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT339o2 (i+1)) + stT339o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 43
    simpa using h
  have hprev := st339o2_p43
  have hstep := st339o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p45 : ((4157326469461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT339o2 (i+1)) + stT339o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 44
    simpa using h
  have hprev := st339o2_p44
  have hstep := st339o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p46 : ((3025745979961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT339o2 (i+1)) + stT339o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 45
    simpa using h
  have hprev := st339o2_p45
  have hstep := st339o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p47 : ((891489579667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT339o2 (i+1)) + stT339o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 46
    simpa using h
  have hprev := st339o2_p46
  have hstep := st339o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p48 : ((3053572769327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT339o2 (i+1)) + stT339o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 47
    simpa using h
  have hprev := st339o2_p47
  have hstep := st339o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p49 : ((4242095269913/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT339o2 (i+1)) + stT339o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 48
    simpa using h
  have hprev := st339o2_p48
  have hstep := st339o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p50 : ((3331017598907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT339o2 (i+1)) + stT339o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 49
    simpa using h
  have hprev := st339o2_p49
  have hstep := st339o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p51 : ((3983770723427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT339o2 (i+1)) + stT339o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 50
    simpa using h
  have hprev := st339o2_p50
  have hstep := st339o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p52 : ((881870970411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT339o2 (i+1)) + stT339o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 51
    simpa using h
  have hprev := st339o2_p51
  have hstep := st339o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p53 : ((966196581361/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT339o2 (i+1)) + stT339o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 52
    simpa using h
  have hprev := st339o2_p52
  have hstep := st339o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p54 : ((222865402159/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT339o2 (i+1)) + stT339o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 53
    simpa using h
  have hprev := st339o2_p53
  have hstep := st339o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p55 : ((3903101250429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT339o2 (i+1)) + stT339o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 54
    simpa using h
  have hprev := st339o2_p54
  have hstep := st339o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p56 : ((172850294677/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT339o2 (i+1)) + stT339o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 55
    simpa using h
  have hprev := st339o2_p55
  have hstep := st339o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p57 : ((508839484369/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT339o2 (i+1)) + stT339o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 56
    simpa using h
  have hprev := st339o2_p56
  have hstep := st339o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p58 : ((1624803216991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT339o2 (i+1)) + stT339o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 57
    simpa using h
  have hprev := st339o2_p57
  have hstep := st339o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p59 : ((4285005265127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT339o2 (i+1)) + stT339o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 58
    simpa using h
  have hprev := st339o2_p58
  have hstep := st339o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p60 : ((3075983283647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT339o2 (i+1)) + stT339o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 59
    simpa using h
  have hprev := st339o2_p59
  have hstep := st339o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p61 : ((4356067041951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT339o2 (i+1)) + stT339o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 60
    simpa using h
  have hprev := st339o2_p60
  have hstep := st339o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p62 : ((3170527794963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT339o2 (i+1)) + stT339o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 61
    simpa using h
  have hprev := st339o2_p61
  have hstep := st339o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p63 : ((202572900407/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT339o2 (i+1)) + stT339o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 62
    simpa using h
  have hprev := st339o2_p62
  have hstep := st339o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p64 : ((3679468960549/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT339o2 (i+1)) + stT339o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 63
    simpa using h
  have hprev := st339o2_p63
  have hstep := st339o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p65 : ((3419007043681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT339o2 (i+1)) + stT339o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 64
    simpa using h
  have hprev := st339o2_p64
  have hstep := st339o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p66 : ((4271635322287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT339o2 (i+1)) + stT339o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 65
    simpa using h
  have hprev := st339o2_p65
  have hstep := st339o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p67 : ((3077452893687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT339o2 (i+1)) + stT339o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 66
    simpa using h
  have hprev := st339o2_p66
  have hstep := st339o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p68 : ((4185873327993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT339o2 (i+1)) + stT339o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 67
    simpa using h
  have hprev := st339o2_p67
  have hstep := st339o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p69 : ((362336178323/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT339o2 (i+1)) + stT339o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 68
    simpa using h
  have hprev := st339o2_p68
  have hstep := st339o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p70 : ((336645926197/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT339o2 (i+1)) + stT339o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 69
    simpa using h
  have hprev := st339o2_p69
  have hstep := st339o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p71 : ((4334418020847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT339o2 (i+1)) + stT339o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 70
    simpa using h
  have hprev := st339o2_p70
  have hstep := st339o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p72 : ((3169794784767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT339o2 (i+1)) + stT339o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 71
    simpa using h
  have hprev := st339o2_p71
  have hstep := st339o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p73 : ((240203884293/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT339o2 (i+1)) + stT339o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 72
    simpa using h
  have hprev := st339o2_p72
  have hstep := st339o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p74 : ((256216991193/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT339o2 (i+1)) + stT339o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 73
    simpa using h
  have hprev := st339o2_p73
  have hstep := st339o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p75 : ((615269114787/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT339o2 (i+1)) + stT339o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 74
    simpa using h
  have hprev := st339o2_p74
  have hstep := st339o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p76 : ((4126280979349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT339o2 (i+1)) + stT339o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 75
    simpa using h
  have hprev := st339o2_p75
  have hstep := st339o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p77 : ((3865824028049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT339o2 (i+1)) + stT339o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 76
    simpa using h
  have hprev := st339o2_p76
  have hstep := st339o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p78 : ((3115821197297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT339o2 (i+1)) + stT339o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 77
    simpa using h
  have hprev := st339o2_p77
  have hstep := st339o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p79 : ((211527251047/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT339o2 (i+1)) + stT339o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 78
    simpa using h
  have hprev := st339o2_p78
  have hstep := st339o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p80 : ((188432022709/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT339o2 (i+1)) + stT339o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 79
    simpa using h
  have hprev := st339o2_p79
  have hstep := st339o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p81 : ((782985541761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT339o2 (i+1)) + stT339o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 80
    simpa using h
  have hprev := st339o2_p80
  have hstep := st339o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p82 : ((4230557797329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT339o2 (i+1)) + stT339o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 81
    simpa using h
  have hprev := st339o2_p81
  have hstep := st339o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p83 : ((3820682534127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT339o2 (i+1)) + stT339o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 82
    simpa using h
  have hprev := st339o2_p82
  have hstep := st339o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p84 : ((3093824562287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT339o2 (i+1)) + stT339o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 83
    simpa using h
  have hprev := st339o2_p83
  have hstep := st339o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p85 : ((4131926552403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT339o2 (i+1)) + stT339o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 84
    simpa using h
  have hprev := st339o2_p84
  have hstep := st339o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p86 : ((4005122727899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT339o2 (i+1)) + stT339o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 85
    simpa using h
  have hprev := st339o2_p85
  have hstep := st339o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p87 : ((306761029871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT339o2 (i+1)) + stT339o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 86
    simpa using h
  have hprev := st339o2_p86
  have hstep := st339o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p88 : ((1942182370631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT339o2 (i+1)) + stT339o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 87
    simpa using h
  have hprev := st339o2_p87
  have hstep := st339o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p89 : ((850226648647/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT339o2 (i+1)) + stT339o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 88
    simpa using h
  have hprev := st339o2_p88
  have hstep := st339o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p90 : ((399683920909/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT339o2 (i+1)) + stT339o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 89
    simpa using h
  have hprev := st339o2_p89
  have hstep := st339o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p91 : ((173945575537/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT339o2 (i+1)) + stT339o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 90
    simpa using h
  have hprev := st339o2_p90
  have hstep := st339o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p92 : ((1091435505059/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT339o2 (i+1)) + stT339o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 91
    simpa using h
  have hprev := st339o2_p91
  have hstep := st339o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p93 : ((180546818191/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT339o2 (i+1)) + stT339o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 92
    simpa using h
  have hprev := st339o2_p92
  have hstep := st339o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p94 : ((1552089569101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT339o2 (i+1)) + stT339o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 93
    simpa using h
  have hprev := st339o2_p93
  have hstep := st339o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p95 : ((2043533031101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT339o2 (i+1)) + stT339o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 94
    simpa using h
  have hprev := st339o2_p94
  have hstep := st339o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p96 : ((2087638614091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT339o2 (i+1)) + stT339o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 95
    simpa using h
  have hprev := st339o2_p95
  have hstep := st339o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p97 : ((3164861768561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT339o2 (i+1)) + stT339o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 96
    simpa using h
  have hprev := st339o2_p96
  have hstep := st339o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p98 : ((686224940757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT339o2 (i+1)) + stT339o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 97
    simpa using h
  have hprev := st339o2_p97
  have hstep := st339o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p99 : ((4350058173921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT339o2 (i+1)) + stT339o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 98
    simpa using h
  have hprev := st339o2_p98
  have hstep := st339o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p100 : ((3827699173921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT339o2 (i+1)) + stT339o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 99
    simpa using h
  have hprev := st339o2_p99
  have hstep := st339o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p101 : ((3044854022459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT339o2 (i+1)) + stT339o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 100
    simpa using h
  have hprev := st339o2_p100
  have hstep := st339o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p102 : ((1865087678593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT339o2 (i+1)) + stT339o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 101
    simpa using h
  have hprev := st339o2_p101
  have hstep := st339o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p103 : ((4382361666299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT339o2 (i+1)) + stT339o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 102
    simpa using h
  have hprev := st339o2_p102
  have hstep := st339o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p104 : ((1802785936893/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT339o2 (i+1)) + stT339o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 103
    simpa using h
  have hprev := st339o2_p103
  have hstep := st339o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p105 : ((3050240289241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT339o2 (i+1)) + stT339o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 104
    simpa using h
  have hprev := st339o2_p104
  have hstep := st339o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p106 : ((1934105432923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT339o2 (i+1)) + stT339o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 105
    simpa using h
  have hprev := st339o2_p105
  have hstep := st339o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p107 : ((437236272311/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT339o2 (i+1)) + stT339o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 106
    simpa using h
  have hprev := st339o2_p106
  have hstep := st339o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p108 : ((709664929099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT339o2 (i+1)) + stT339o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 107
    simpa using h
  have hprev := st339o2_p107
  have hstep := st339o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p109 : ((3046582296777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT339o2 (i+1)) + stT339o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 108
    simpa using h
  have hprev := st339o2_p108
  have hstep := st339o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p110 : ((3847126154293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT339o2 (i+1)) + stT339o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 109
    simpa using h
  have hprev := st339o2_p109
  have hstep := st339o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p111 : ((548946156699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT339o2 (i+1)) + stT339o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 110
    simpa using h
  have hprev := st339o2_p110
  have hstep := st339o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p112 : ((455745706491/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT339o2 (i+1)) + stT339o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 111
    simpa using h
  have hprev := st339o2_p111
  have hstep := st339o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p113 : ((47212583771/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT339o2 (i+1)) + stT339o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 112
    simpa using h
  have hprev := st339o2_p112
  have hstep := st339o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p114 : ((3672002765819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT339o2 (i+1)) + stT339o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 113
    simpa using h
  have hprev := st339o2_p113
  have hstep := st339o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p115 : ((4398643452763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT339o2 (i+1)) + stT339o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 114
    simpa using h
  have hprev := st339o2_p114
  have hstep := st339o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p116 : ((389443494639/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT339o2 (i+1)) + stT339o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 115
    simpa using h
  have hprev := st339o2_p115
  have hstep := st339o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p117 : ((3065234282973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT339o2 (i+1)) + stT339o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 116
    simpa using h
  have hprev := st339o2_p116
  have hstep := st339o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p118 : ((3363433057071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT339o2 (i+1)) + stT339o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 117
    simpa using h
  have hprev := st339o2_p117
  have hstep := st339o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p119 : ((4263673577877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT339o2 (i+1)) + stT339o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 118
    simpa using h
  have hprev := st339o2_p118
  have hstep := st339o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p120 : ((845946241671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT339o2 (i+1)) + stT339o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 119
    simpa using h
  have hprev := st339o2_p119
  have hstep := st339o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p121 : ((332791748181/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT339o2 (i+1)) + stT339o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 120
    simpa using h
  have hprev := st339o2_p120
  have hstep := st339o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p122 : ((191122194831/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT339o2 (i+1)) + stT339o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 121
    simpa using h
  have hprev := st339o2_p121
  have hstep := st339o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p123 : ((120423267587/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT339o2 (i+1)) + stT339o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 122
    simpa using h
  have hprev := st339o2_p122
  have hstep := st339o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p124 : ((2211930110393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT339o2 (i+1)) + stT339o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 123
    simpa using h
  have hprev := st339o2_p123
  have hstep := st339o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p125 : ((386608865899/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT339o2 (i+1)) + stT339o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 124
    simpa using h
  have hprev := st339o2_p124
  have hstep := st339o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p126 : ((613013290739/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT339o2 (i+1)) + stT339o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 125
    simpa using h
  have hprev := st339o2_p125
  have hstep := st339o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p127 : ((3260588249447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT339o2 (i+1)) + stT339o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 126
    simpa using h
  have hprev := st339o2_p126
  have hstep := st339o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p128 : ((165770576833/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT339o2 (i+1)) + stT339o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 127
    simpa using h
  have hprev := st339o2_p127
  have hstep := st339o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p129 : ((175192131411/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT339o2 (i+1)) + stT339o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 128
    simpa using h
  have hprev := st339o2_p128
  have hstep := st339o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p130 : ((3624266072079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT339o2 (i+1)) + stT339o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 129
    simpa using h
  have hprev := st339o2_p129
  have hstep := st339o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p131 : ((1497298244667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT339o2 (i+1)) + stT339o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 130
    simpa using h
  have hprev := st339o2_p130
  have hstep := st339o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p132 : ((1699881051667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT339o2 (i+1)) + stT339o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 131
    simpa using h
  have hprev := st339o2_p131
  have hstep := st339o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p133 : ((850155338637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT339o2 (i+1)) + stT339o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 132
    simpa using h
  have hprev := st339o2_p132
  have hstep := st339o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p134 : ((4344210928329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT339o2 (i+1)) + stT339o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 133
    simpa using h
  have hprev := st339o2_p133
  have hstep := st339o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p135 : ((1778976552671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT339o2 (i+1)) + stT339o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 134
    simpa using h
  have hprev := st339o2_p134
  have hstep := st339o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p136 : ((2980434142321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT339o2 (i+1)) + stT339o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 135
    simpa using h
  have hprev := st339o2_p135
  have hstep := st339o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p137 : ((1696086778487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT339o2 (i+1)) + stT339o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 136
    simpa using h
  have hprev := st339o2_p136
  have hstep := st339o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p138 : ((2115924109547/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT339o2 (i+1)) + stT339o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 137
    simpa using h
  have hprev := st339o2_p137
  have hstep := st339o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p139 : ((17541691339/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT339o2 (i+1)) + stT339o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 138
    simpa using h
  have hprev := st339o2_p138
  have hstep := st339o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p140 : ((731910433259/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT339o2 (i+1)) + stT339o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 139
    simpa using h
  have hprev := st339o2_p139
  have hstep := st339o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p141 : ((2998653172647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT339o2 (i+1)) + stT339o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 140
    simpa using h
  have hprev := st339o2_p140
  have hstep := st339o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p142 : ((3243108276309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT339o2 (i+1)) + stT339o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 141
    simpa using h
  have hprev := st339o2_p141
  have hstep := st339o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p143 : ((4076241128553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT339o2 (i+1)) + stT339o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 142
    simpa using h
  have hprev := st339o2_p142
  have hstep := st339o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p144 : ((4457530976037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT339o2 (i+1)) + stT339o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 143
    simpa using h
  have hprev := st339o2_p143
  have hstep := st339o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p145 : ((3923937063977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT339o2 (i+1)) + stT339o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 144
    simpa using h
  have hprev := st339o2_p144
  have hstep := st339o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p146 : ((3131296589871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT339o2 (i+1)) + stT339o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 145
    simpa using h
  have hprev := st339o2_p145
  have hstep := st339o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p147 : ((378869022333/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT339o2 (i+1)) + stT339o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 146
    simpa using h
  have hprev := st339o2_p146
  have hstep := st339o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p148 : ((233402353731/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT339o2 (i+1)) + stT339o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 147
    simpa using h
  have hprev := st339o2_p147
  have hstep := st339o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p149 : ((4411516515807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT339o2 (i+1)) + stT339o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 148
    simpa using h
  have hprev := st339o2_p148
  have hstep := st339o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p150 : ((2140353173967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT339o2 (i+1)) + stT339o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 149
    simpa using h
  have hprev := st339o2_p149
  have hstep := st339o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p151 : ((139976119641/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT339o2 (i+1)) + stT339o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 150
    simpa using h
  have hprev := st339o2_p150
  have hstep := st339o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p152 : ((2955045701201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT339o2 (i+1)) + stT339o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 151
    simpa using h
  have hprev := st339o2_p151
  have hstep := st339o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p153 : ((3251733841517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT339o2 (i+1)) + stT339o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 152
    simpa using h
  have hprev := st339o2_p152
  have hstep := st339o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p154 : ((4054200398709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT339o2 (i+1)) + stT339o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 153
    simpa using h
  have hprev := st339o2_p153
  have hstep := st339o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p155 : ((560479979019/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT339o2 (i+1)) + stT339o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 154
    simpa using h
  have hprev := st339o2_p154
  have hstep := st339o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p156 : ((510262174217/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT339o2 (i+1)) + stT339o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 155
    simpa using h
  have hprev := st339o2_p155
  have hstep := st339o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p157 : ((656908543553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT339o2 (i+1)) + stT339o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 156
    simpa using h
  have hprev := st339o2_p156
  have hstep := st339o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p158 : ((2933642768473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT339o2 (i+1)) + stT339o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 157
    simpa using h
  have hprev := st339o2_p157
  have hstep := st339o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p159 : ((1694824736313/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT339o2 (i+1)) + stT339o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 158
    simpa using h
  have hprev := st339o2_p158
  have hstep := st339o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p160 : ((4175860065729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT339o2 (i+1)) + stT339o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 159
    simpa using h
  have hprev := st339o2_p159
  have hstep := st339o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p161 : ((4490081098949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT339o2 (i+1)) + stT339o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 160
    simpa using h
  have hprev := st339o2_p160
  have hstep := st339o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p162 : ((1005306403581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT339o2 (i+1)) + stT339o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 161
    simpa using h
  have hprev := st339o2_p161
  have hstep := st339o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p163 : ((3242804384043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT339o2 (i+1)) + stT339o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 162
    simpa using h
  have hprev := st339o2_p162
  have hstep := st339o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p164 : ((116905236597/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT339o2 (i+1)) + stT339o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 163
    simpa using h
  have hprev := st339o2_p163
  have hstep := st339o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p165 : ((26938160381/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT339o2 (i+1)) + stT339o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 164
    simpa using h
  have hprev := st339o2_p164
  have hstep := st339o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p166 : ((165676852079/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT339o2 (i+1)) + stT339o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 165
    simpa using h
  have hprev := st339o2_p165
  have hstep := st339o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p167 : ((2253516717121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT339o2 (i+1)) + stT339o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 166
    simpa using h
  have hprev := st339o2_p166
  have hstep := st339o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p168 : ((4123301709401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT339o2 (i+1)) + stT339o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 167
    simpa using h
  have hprev := st339o2_p167
  have hstep := st339o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p169 : ((838697100481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT339o2 (i+1)) + stT339o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 168
    simpa using h
  have hprev := st339o2_p168
  have hstep := st339o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p170 : ((1456079547527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT339o2 (i+1)) + stT339o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 169
    simpa using h
  have hprev := st339o2_p169
  have hstep := st339o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p171 : ((399382596419/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT339o2 (i+1)) + stT339o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 170
    simpa using h
  have hprev := st339o2_p170
  have hstep := st339o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p172 : ((98544687169/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT339o2 (i+1)) + stT339o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 171
    simpa using h
  have hprev := st339o2_p171
  have hstep := st339o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p173 : ((896540122629/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT339o2 (i+1)) + stT339o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 172
    simpa using h
  have hprev := st339o2_p172
  have hstep := st339o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p174 : ((4342989032237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT339o2 (i+1)) + stT339o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 173
    simpa using h
  have hprev := st339o2_p173
  have hstep := st339o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p175 : ((3650926961589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT339o2 (i+1)) + stT339o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 174
    simpa using h
  have hprev := st339o2_p174
  have hstep := st339o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p176 : ((300893263351/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT339o2 (i+1)) + stT339o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 175
    simpa using h
  have hprev := st339o2_p175
  have hstep := st339o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p177 : ((148237165319/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT339o2 (i+1)) + stT339o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 176
    simpa using h
  have hprev := st339o2_p176
  have hstep := st339o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p178 : ((3550037823191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT339o2 (i+1)) + stT339o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 177
    simpa using h
  have hprev := st339o2_p177
  have hstep := st339o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p179 : ((2134680522703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT339o2 (i+1)) + stT339o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 178
    simpa using h
  have hprev := st339o2_p178
  have hstep := st339o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p180 : ((2262999348793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT339o2 (i+1)) + stT339o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 179
    simpa using h
  have hprev := st339o2_p179
  have hstep := st339o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p181 : ((2056983246823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT339o2 (i+1)) + stT339o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 180
    simpa using h
  have hprev := st339o2_p180
  have hstep := st339o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p182 : ((843396124349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT339o2 (i+1)) + stT339o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 181
    simpa using h
  have hprev := st339o2_p181
  have hstep := st339o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p183 : ((1451092422831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT339o2 (i+1)) + stT339o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 182
    simpa using h
  have hprev := st339o2_p182
  have hstep := st339o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p184 : ((3071842438877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT339o2 (i+1)) + stT339o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 183
    simpa using h
  have hprev := st339o2_p183
  have hstep := st339o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p185 : ((748635032969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT339o2 (i+1)) + stT339o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 184
    simpa using h
  have hprev := st339o2_p184
  have hstep := st339o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p186 : ((877747744473/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT339o2 (i+1)) + stT339o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 185
    simpa using h
  have hprev := st339o2_p185
  have hstep := st339o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p187 : ((4510992044053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT339o2 (i+1)) + stT339o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 186
    simpa using h
  have hprev := st339o2_p186
  have hstep := st339o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p188 : ((502668960341/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT339o2 (i+1)) + stT339o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 187
    simpa using h
  have hprev := st339o2_p187
  have hstep := st339o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p189 : ((3295430198767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT339o2 (i+1)) + stT339o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 188
    simpa using h
  have hprev := st339o2_p188
  have hstep := st339o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p190 : ((179914548757/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT339o2 (i+1)) + stT339o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 189
    simpa using h
  have hprev := st339o2_p189
  have hstep := st339o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p191 : ((15385227269/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT339o2 (i+1)) + stT339o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 190
    simpa using h
  have hprev := st339o2_p190
  have hstep := st339o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p192 : ((3739497106527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT339o2 (i+1)) + stT339o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 191
    simpa using h
  have hprev := st339o2_p191
  have hstep := st339o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p193 : ((4380357038807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT339o2 (i+1)) + stT339o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 192
    simpa using h
  have hprev := st339o2_p192
  have hstep := st339o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p194 : ((4538516006627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT339o2 (i+1)) + stT339o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 193
    simpa using h
  have hprev := st339o2_p193
  have hstep := st339o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p195 : ((4105494156197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT339o2 (i+1)) + stT339o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 194
    simpa using h
  have hprev := st339o2_p194
  have hstep := st339o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p196 : ((3392232442321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT339o2 (i+1)) + stT339o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 195
    simpa using h
  have hprev := st339o2_p195
  have hstep := st339o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p197 : ((1449989908091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT339o2 (i+1)) + stT339o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 196
    simpa using h
  have hprev := st339o2_p196
  have hstep := st339o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p198 : ((593549416003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT339o2 (i+1)) + stT339o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 197
    simpa using h
  have hprev := st339o2_p197
  have hstep := st339o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p199 : ((1772051742973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT339o2 (i+1)) + stT339o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 198
    simpa using h
  have hprev := st339o2_p198
  have hstep := st339o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p200 : ((529103709961/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT339o2 (i+1)) + stT339o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 199
    simpa using h
  have hprev := st339o2_p199
  have hstep := st339o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p201 : ((4569168505523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT339o2 (i+1)) + stT339o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 200
    simpa using h
  have hprev := st339o2_p200
  have hstep := st339o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p202 : ((4331800573449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT339o2 (i+1)) + stT339o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 201
    simpa using h
  have hprev := st339o2_p201
  have hstep := st339o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p203 : ((3682523956861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT339o2 (i+1)) + stT339o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 202
    simpa using h
  have hprev := st339o2_p202
  have hstep := st339o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p204 : ((6100003749/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT339o2 (i+1)) + stT339o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 203
    simpa using h
  have hprev := st339o2_p203
  have hstep := st339o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p205 : ((2844426392391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT339o2 (i+1)) + stT339o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 204
    simpa using h
  have hprev := st339o2_p204
  have hstep := st339o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p206 : ((63885441131/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT339o2 (i+1)) + stT339o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 205
    simpa using h
  have hprev := st339o2_p205
  have hstep := st339o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p207 : ((1935970538179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT339o2 (i+1)) + stT339o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 206
    simpa using h
  have hprev := st339o2_p206
  have hstep := st339o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p208 : ((4446898026983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT339o2 (i+1)) + stT339o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 207
    simpa using h
  have hprev := st339o2_p207
  have hstep := st339o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p209 : ((4560366791543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT339o2 (i+1)) + stT339o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 208
    simpa using h
  have hprev := st339o2_p208
  have hstep := st339o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p210 : ((4145885549303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT339o2 (i+1)) + stT339o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 209
    simpa using h
  have hprev := st339o2_p209
  have hstep := st339o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p211 : ((3462483457861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT339o2 (i+1)) + stT339o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 210
    simpa using h
  have hprev := st339o2_p210
  have hstep := st339o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p212 : ((732111340587/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT339o2 (i+1)) + stT339o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 211
    simpa using h
  have hprev := st339o2_p211
  have hstep := st339o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p213 : ((2864737174317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT339o2 (i+1)) + stT339o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 212
    simpa using h
  have hprev := st339o2_p212
  have hstep := st339o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p214 : ((826382126193/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT339o2 (i+1)) + stT339o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 213
    simpa using h
  have hprev := st339o2_p213
  have hstep := st339o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p215 : ((1992660855067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT339o2 (i+1)) + stT339o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 214
    simpa using h
  have hprev := st339o2_p214
  have hstep := st339o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p216 : ((45026955079/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT339o2 (i+1)) + stT339o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 215
    simpa using h
  have hprev := st339o2_p215
  have hstep := st339o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p217 : ((1139409606471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT339o2 (i+1)) + stT339o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 216
    simpa using h
  have hprev := st339o2_p216
  have hstep := st339o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p218 : ((2061099871311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT339o2 (i+1)) + stT339o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 217
    simpa using h
  have hprev := st339o2_p217
  have hstep := st339o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p219 : ((1724795880519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT339o2 (i+1)) + stT339o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 218
    simpa using h
  have hprev := st339o2_p218
  have hstep := st339o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p220 : ((1461686296619/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT339o2 (i+1)) + stT339o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 219
    simpa using h
  have hprev := st339o2_p219
  have hstep := st339o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p221 : ((709587690519/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT339o2 (i+1)) + stT339o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 220
    simpa using h
  have hprev := st339o2_p220
  have hstep := st339o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p222 : ((809585907583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT339o2 (i+1)) + stT339o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 221
    simpa using h
  have hprev := st339o2_p221
  have hstep := st339o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p223 : ((1949127297287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT339o2 (i+1)) + stT339o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 222
    simpa using h
  have hprev := st339o2_p222
  have hstep := st339o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p224 : ((4454181275929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT339o2 (i+1)) + stT339o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 223
    simpa using h
  have hprev := st339o2_p223
  have hstep := st339o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p225 : ((4604727125383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT339o2 (i+1)) + stT339o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 224
    simpa using h
  have hprev := st339o2_p224
  have hstep := st339o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p226 : ((427196998397/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT339o2 (i+1)) + stT339o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 225
    simpa using h
  have hprev := st339o2_p225
  have hstep := st339o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p227 : ((1818793947281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT339o2 (i+1)) + stT339o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 226
    simpa using h
  have hprev := st339o2_p226
  have hstep := st339o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p228 : ((1520096960407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT339o2 (i+1)) + stT339o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 227
    simpa using h
  have hprev := st339o2_p227
  have hstep := st339o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p229 : ((2793475164707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT339o2 (i+1)) + stT339o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 228
    simpa using h
  have hprev := st339o2_p228
  have hstep := st339o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p230 : ((3023251950827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT339o2 (i+1)) + stT339o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 229
    simpa using h
  have hprev := st339o2_p229
  have hstep := st339o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p231 : ((90174701297/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT339o2 (i+1)) + stT339o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 230
    simpa using h
  have hprev := st339o2_p230
  have hstep := st339o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p232 : ((1060657793309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT339o2 (i+1)) + stT339o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 231
    simpa using h
  have hprev := st339o2_p231
  have hstep := st339o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p233 : ((230327675461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT339o2 (i+1)) + stT339o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 232
    simpa using h
  have hprev := st339o2_p232
  have hstep := st339o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p234 : ((4517313401789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT339o2 (i+1)) + stT339o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 233
    simpa using h
  have hprev := st339o2_p233
  have hstep := st339o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p235 : ((2011522185409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT339o2 (i+1)) + stT339o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 234
    simpa using h
  have hprev := st339o2_p234
  have hstep := st339o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p236 : ((3372090908533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT339o2 (i+1)) + stT339o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 235
    simpa using h
  have hprev := st339o2_p235
  have hstep := st339o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p237 : ((2886007284413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT339o2 (i+1)) + stT339o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 236
    simpa using h
  have hprev := st339o2_p236
  have hstep := st339o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p238 : ((2800811888081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT339o2 (i+1)) + stT339o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 237
    simpa using h
  have hprev := st339o2_p237
  have hstep := st339o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p239 : ((3154689044607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT339o2 (i+1)) + stT339o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 238
    simpa using h
  have hprev := st339o2_p238
  have hstep := st339o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p240 : ((1887136283771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT339o2 (i+1)) + stT339o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 239
    simpa using h
  have hprev := st339o2_p239
  have hstep := st339o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p241 : ((2181121030221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT339o2 (i+1)) + stT339o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 240
    simpa using h
  have hprev := st339o2_p240
  have hstep := st339o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p242 : ((2320411027249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT339o2 (i+1)) + stT339o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 241
    simpa using h
  have hprev := st339o2_p241
  have hstep := st339o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p243 : ((4481654750881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT339o2 (i+1)) + stT339o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 242
    simpa using h
  have hprev := st339o2_p242
  have hstep := st339o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p244 : ((3962085726361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT339o2 (i+1)) + stT339o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 243
    simpa using h
  have hprev := st339o2_p243
  have hstep := st339o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p245 : ((3324707531803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT339o2 (i+1)) + stT339o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 244
    simpa using h
  have hprev := st339o2_p244
  have hstep := st339o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p246 : ((114495660921/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT339o2 (i+1)) + stT339o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 245
    simpa using h
  have hprev := st339o2_p245
  have hstep := st339o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p247 : ((556795660953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT339o2 (i+1)) + stT339o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 246
    simpa using h
  have hprev := st339o2_p246
  have hstep := st339o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p248 : ((624394966953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT339o2 (i+1)) + stT339o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 247
    simpa using h
  have hprev := st339o2_p247
  have hstep := st339o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p249 : ((3722012601821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT339o2 (i+1)) + stT339o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 248
    simpa using h
  have hprev := st339o2_p248
  have hstep := st339o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p250 : ((2157827235463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT339o2 (i+1)) + stT339o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 249
    simpa using h
  have hprev := st339o2_p249
  have hstep := st339o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p251 : ((2320650670897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 250, stT339o2 (i+1)) + stT339o2 251 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 250
    simpa using h
  have hprev := st339o2_p250
  have hstep := st339o2_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p252 : ((2279239609439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 251, stT339o2 (i+1)) + stT339o2 252 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 251
    simpa using h
  have hprev := st339o2_p251
  have hstep := st339o2_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p253 : ((4106096073373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 252, stT339o2 (i+1)) + stT339o2 253 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 252
    simpa using h
  have hprev := st339o2_p252
  have hstep := st339o2_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p254 : ((696336897977/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 253, stT339o2 (i+1)) + stT339o2 254 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 253
    simpa using h
  have hprev := st339o2_p253
  have hstep := st339o2_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p255 : ((73835199209/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 254, stT339o2 (i+1)) + stT339o2 255 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 254
    simpa using h
  have hprev := st339o2_p254
  have hstep := st339o2_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p256 : ((171543289651/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 255, stT339o2 (i+1)) + stT339o2 256 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 255
    simpa using h
  have hprev := st339o2_p255
  have hstep := st339o2_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p257 : ((735276965753/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 256, stT339o2 (i+1)) + stT339o2 257 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 256
    simpa using h
  have hprev := st339o2_p256
  have hstep := st339o2_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p258 : ((864411783851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 257, stT339o2 (i+1)) + stT339o2 258 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 257
    simpa using h
  have hprev := st339o2_p257
  have hstep := st339o2_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p259 : ((4077730522943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 258, stT339o2 (i+1)) + stT339o2 259 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 258
    simpa using h
  have hprev := st339o2_p258
  have hstep := st339o2_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p260 : ((4545282668681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 259, stT339o2 (i+1)) + stT339o2 260 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 259
    simpa using h
  have hprev := st339o2_p259
  have hstep := st339o2_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p261 : ((4670278440689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 260, stT339o2 (i+1)) + stT339o2 261 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 260
    simpa using h
  have hprev := st339o2_p260
  have hstep := st339o2_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p262 : ((4404421746911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 261, stT339o2 (i+1)) + stT339o2 262 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 261
    simpa using h
  have hprev := st339o2_p261
  have hstep := st339o2_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p263 : ((3857527861087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 262, stT339o2 (i+1)) + stT339o2 263 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 262
    simpa using h
  have hprev := st339o2_p262
  have hstep := st339o2_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p264 : ((3250195137603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 263, stT339o2 (i+1)) + stT339o2 264 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 263
    simpa using h
  have hprev := st339o2_p263
  have hstep := st339o2_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p265 : ((112954506251/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 264, stT339o2 (i+1)) + stT339o2 265 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 264
    simpa using h
  have hprev := st339o2_p264
  have hstep := st339o2_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p266 : ((21961770559/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 265, stT339o2 (i+1)) + stT339o2 266 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 265
    simpa using h
  have hprev := st339o2_p265
  have hstep := st339o2_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p267 : ((608517574573/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 266, stT339o2 (i+1)) + stT339o2 267 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 266
    simpa using h
  have hprev := st339o2_p266
  have hstep := st339o2_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p268 : ((1798935809449/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 267, stT339o2 (i+1)) + stT339o2 268 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 267
    simpa using h
  have hprev := st339o2_p267
  have hstep := st339o2_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p269 : ((524400639451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 268, stT339o2 (i+1)) + stT339o2 269 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 268
    simpa using h
  have hprev := st339o2_p268
  have hstep := st339o2_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p270 : ((1151413191977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 269, stT339o2 (i+1)) + stT339o2 270 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 269
    simpa using h
  have hprev := st339o2_p269
  have hstep := st339o2_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p271 : ((1168626672649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 270, stT339o2 (i+1)) + stT339o2 271 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 270
    simpa using h
  have hprev := st339o2_p270
  have hstep := st339o2_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p272 : ((547265734947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 271, stT339o2 (i+1)) + stT339o2 272 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 271
    simpa using h
  have hprev := st339o2_p271
  have hstep := st339o2_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p273 : ((478753925347/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 272, stT339o2 (i+1)) + stT339o2 273 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 272
    simpa using h
  have hprev := st339o2_p272
  have hstep := st339o2_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p274 : ((3235816624099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 273, stT339o2 (i+1)) + stT339o2 274 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 273
    simpa using h
  have hprev := st339o2_p273
  have hstep := st339o2_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p275 : ((2815270795991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 274, stT339o2 (i+1)) + stT339o2 275 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 274
    simpa using h
  have hprev := st339o2_p274
  have hstep := st339o2_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p276 : ((2721460607421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 275, stT339o2 (i+1)) + stT339o2 276 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 275
    simpa using h
  have hprev := st339o2_p275
  have hstep := st339o2_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p277 : ((119453510289/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 276, stT339o2 (i+1)) + stT339o2 277 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 276
    simpa using h
  have hprev := st339o2_p276
  have hstep := st339o2_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p278 : ((702333628197/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 277, stT339o2 (i+1)) + stT339o2 278 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 277
    simpa using h
  have hprev := st339o2_p277
  have hstep := st339o2_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p279 : ((821402296853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 278, stT339o2 (i+1)) + stT339o2 279 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 278
    simpa using h
  have hprev := st339o2_p278
  have hstep := st339o2_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p280 : ((4559538550187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 279, stT339o2 (i+1)) + stT339o2 280 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 279
    simpa using h
  have hprev := st339o2_p279
  have hstep := st339o2_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p281 : ((4709904691127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 280, stT339o2 (i+1)) + stT339o2 281 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 280
    simpa using h
  have hprev := st339o2_p280
  have hstep := st339o2_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p282 : ((4507208742199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 281, stT339o2 (i+1)) + stT339o2 282 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 281
    simpa using h
  have hprev := st339o2_p281
  have hstep := st339o2_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p283 : ((251537485497/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 282, stT339o2 (i+1)) + stT339o2 283 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 282
    simpa using h
  have hprev := st339o2_p282
  have hstep := st339o2_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p284 : ((3431374324041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 283, stT339o2 (i+1)) + stT339o2 284 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 283
    simpa using h
  have hprev := st339o2_p283
  have hstep := st339o2_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p285 : ((1466345254833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 284, stT339o2 (i+1)) + stT339o2 285 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 284
    simpa using h
  have hprev := st339o2_p284
  have hstep := st339o2_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p286 : ((168663408007/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 285, stT339o2 (i+1)) + stT339o2 286 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 285
    simpa using h
  have hprev := st339o2_p285
  have hstep := st339o2_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p287 : ((280697713353/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 286, stT339o2 (i+1)) + stT339o2 287 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 286
    simpa using h
  have hprev := st339o2_p286
  have hstep := st339o2_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p288 : ((321893473211/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 287, stT339o2 (i+1)) + stT339o2 288 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 287
    simpa using h
  have hprev := st339o2_p287
  have hstep := st339o2_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p289 : ((379433444441/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 288, stT339o2 (i+1)) + stT339o2 289 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 288
    simpa using h
  have hprev := st339o2_p288
  have hstep := st339o2_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p290 : ((3472322593/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 289, stT339o2 (i+1)) + stT339o2 290 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 289
    simpa using h
  have hprev := st339o2_p289
  have hstep := st339o2_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p291 : ((467661109013/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 290, stT339o2 (i+1)) + stT339o2 291 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 290
    simpa using h
  have hprev := st339o2_p290
  have hstep := st339o2_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p292 : ((117344320299/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 291, stT339o2 (i+1)) + stT339o2 292 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 291
    simpa using h
  have hprev := st339o2_p291
  have hstep := st339o2_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p293 : ((4388333618771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 292, stT339o2 (i+1)) + stT339o2 293 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 292
    simpa using h
  have hprev := st339o2_p292
  have hstep := st339o2_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p294 : ((3861436569491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 293, stT339o2 (i+1)) + stT339o2 294 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 293
    simpa using h
  have hprev := st339o2_p293
  have hstep := st339o2_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p295 : ((656855549029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 294, stT339o2 (i+1)) + stT339o2 295 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 294
    simpa using h
  have hprev := st339o2_p294
  have hstep := st339o2_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p296 : ((355242105967/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 295, stT339o2 (i+1)) + stT339o2 296 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 295
    simpa using h
  have hprev := st339o2_p295
  have hstep := st339o2_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p297 : ((2674229811297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 296, stT339o2 (i+1)) + stT339o2 297 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 296
    simpa using h
  have hprev := st339o2_p296
  have hstep := st339o2_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p298 : ((2832389404681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 297, stT339o2 (i+1)) + stT339o2 298 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 297
    simpa using h
  have hprev := st339o2_p297
  have hstep := st339o2_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p299 : ((3264703987183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 298, stT339o2 (i+1)) + stT339o2 299 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 298
    simpa using h
  have hprev := st339o2_p298
  have hstep := st339o2_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p300 : ((3834611945683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 299, stT339o2 (i+1)) + stT339o2 300 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 299
    simpa using h
  have hprev := st339o2_p299
  have hstep := st339o2_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p301 : ((4364652696613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 300, stT339o2 (i+1)) + stT339o2 301 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 300
    simpa using h
  have hprev := st339o2_p300
  have hstep := st339o2_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p302 : ((4691889921543/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 301, stT339o2 (i+1)) + stT339o2 302 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 301
    simpa using h
  have hprev := st339o2_p301
  have hstep := st339o2_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p303 : ((4717489503067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 302, stT339o2 (i+1)) + stT339o2 303 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 302
    simpa using h
  have hprev := st339o2_p302
  have hstep := st339o2_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p304 : ((4435541827387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 303, stT339o2 (i+1)) + stT339o2 304 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 303
    simpa using h
  have hprev := st339o2_p303
  have hstep := st339o2_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p305 : ((3933091930877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 304, stT339o2 (i+1)) + stT339o2 305 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 304
    simpa using h
  have hprev := st339o2_p304
  have hstep := st339o2_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p306 : ((3362251409171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 305, stT339o2 (i+1)) + stT339o2 306 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 305
    simpa using h
  have hprev := st339o2_p305
  have hstep := st339o2_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p307 : ((180851618579/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 306, stT339o2 (i+1)) + stT339o2 307 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 306
    simpa using h
  have hprev := st339o2_p306
  have hstep := st339o2_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p308 : ((2665408969507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 307, stT339o2 (i+1)) + stT339o2 308 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 307
    simpa using h
  have hprev := st339o2_p307
  have hstep := st339o2_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p309 : ((2743302294627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 308, stT339o2 (i+1)) + stT339o2 309 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 308
    simpa using h
  have hprev := st339o2_p308
  have hstep := st339o2_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p310 : ((387829201567/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 309, stT339o2 (i+1)) + stT339o2 310 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 309
    simpa using h
  have hprev := st339o2_p309
  have hstep := st339o2_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p311 : ((72744479527/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 310, stT339o2 (i+1)) + stT339o2 311 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 310
    simpa using h
  have hprev := st339o2_p310
  have hstep := st339o2_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p312 : ((523944962183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 311, stT339o2 (i+1)) + stT339o2 312 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 311
    simpa using h
  have hprev := st339o2_p311
  have hstep := st339o2_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p313 : ((4606374587203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 312, stT339o2 (i+1)) + stT339o2 313 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 312
    simpa using h
  have hprev := st339o2_p312
  have hstep := st339o2_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p314 : ((4764158992743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 313, stT339o2 (i+1)) + stT339o2 314 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 313
    simpa using h
  have hprev := st339o2_p313
  have hstep := st339o2_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p315 : ((2310857397231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 314, stT339o2 (i+1)) + stT339o2 315 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 314
    simpa using h
  have hprev := st339o2_p314
  have hstep := st339o2_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p316 : ((2110490756583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 315, stT339o2 (i+1)) + stT339o2 316 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 315
    simpa using h
  have hprev := st339o2_p315
  have hstep := st339o2_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p317 : ((367572811499/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 316, stT339o2 (i+1)) + stT339o2 317 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 316
    simpa using h
  have hprev := st339o2_p316
  have hstep := st339o2_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p318 : ((3138564219063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 317, stT339o2 (i+1)) + stT339o2 318 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 317
    simpa using h
  have hprev := st339o2_p317
  have hstep := st339o2_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p319 : ((1379015630967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 318, stT339o2 (i+1)) + stT339o2 319 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 318
    simpa using h
  have hprev := st339o2_p318
  have hstep := st339o2_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p320 : ((329724875451/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 319, stT339o2 (i+1)) + stT339o2 320 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 319
    simpa using h
  have hprev := st339o2_p319
  have hstep := st339o2_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p321 : ((2809182449163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 320, stT339o2 (i+1)) + stT339o2 321 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 320
    simpa using h
  have hprev := st339o2_p320
  have hstep := st339o2_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p322 : ((3223892018423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 321, stT339o2 (i+1)) + stT339o2 322 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 321
    simpa using h
  have hprev := st339o2_p321
  have hstep := st339o2_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p323 : ((3768531741769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 322, stT339o2 (i+1)) + stT339o2 323 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 322
    simpa using h
  have hprev := st339o2_p322
  have hstep := st339o2_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p324 : ((1074046275751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 323, stT339o2 (i+1)) + stT339o2 324 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 323
    simpa using h
  have hprev := st339o2_p323
  have hstep := st339o2_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p325 : ((583276866713/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 324, stT339o2 (i+1)) + stT339o2 325 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 324
    simpa using h
  have hprev := st339o2_p324
  have hstep := st339o2_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p326 : ((119535826021/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 325, stT339o2 (i+1)) + stT339o2 326 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 325
    simpa using h
  have hprev := st339o2_p325
  have hstep := st339o2_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p327 : ((1153238586379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 326, stT339o2 (i+1)) + stT339o2 327 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 326
    simpa using h
  have hprev := st339o2_p326
  have hstep := st339o2_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p328 : ((2103277231099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 327, stT339o2 (i+1)) + stT339o2 328 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 327
    simpa using h
  have hprev := st339o2_p327
  have hstep := st339o2_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p329 : ((229340142069/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 328, stT339o2 (i+1)) + stT339o2 329 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 328
    simpa using h
  have hprev := st339o2_p328
  have hstep := st339o2_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p330 : ((785350305579/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 329, stT339o2 (i+1)) + stT339o2 330 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 329
    simpa using h
  have hprev := st339o2_p329
  have hstep := st339o2_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p331 : ((689562800079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 330, stT339o2 (i+1)) + stT339o2 331 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 330
    simpa using h
  have hprev := st339o2_p330
  have hstep := st339o2_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p332 : ((81786491377/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 331, stT339o2 (i+1)) + stT339o2 332 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 331
    simpa using h
  have hprev := st339o2_p331
  have hstep := st339o2_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p333 : ((688157672819/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 332, stT339o2 (i+1)) + stT339o2 333 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 332
    simpa using h
  have hprev := st339o2_p332
  have hstep := st339o2_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p334 : ((3128803107451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 333, stT339o2 (i+1)) + stT339o2 334 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 333
    simpa using h
  have hprev := st339o2_p333
  have hstep := st339o2_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p335 : ((3649757645883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 334, stT339o2 (i+1)) + stT339o2 335 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 334
    simpa using h
  have hprev := st339o2_p334
  have hstep := st339o2_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p336 : ((167379296691/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 335, stT339o2 (i+1)) + stT339o2 336 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 335
    simpa using h
  have hprev := st339o2_p335
  have hstep := st339o2_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p337 : ((4600051270131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 336, stT339o2 (i+1)) + stT339o2 337 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 336
    simpa using h
  have hprev := st339o2_p336
  have hstep := st339o2_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p338 : ((4794497915139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 337, stT339o2 (i+1)) + stT339o2 338 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 337
    simpa using h
  have hprev := st339o2_p337
  have hstep := st339o2_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p339 : ((4721303539749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 338, stT339o2 (i+1)) + stT339o2 339 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 338
    simpa using h
  have hprev := st339o2_p338
  have hstep := st339o2_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p340 : ((1099961836351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 339, stT339o2 (i+1)) + stT339o2 340 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 339
    simpa using h
  have hprev := st339o2_p339
  have hstep := st339o2_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p341 : ((488693959547/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 340, stT339o2 (i+1)) + stT339o2 341 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 340
    simpa using h
  have hprev := st339o2_p340
  have hstep := st339o2_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p342 : ((16848432553/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 341, stT339o2 (i+1)) + stT339o2 342 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 341
    simpa using h
  have hprev := st339o2_p341
  have hstep := st339o2_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p343 : ((58201567417/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 342, stT339o2 (i+1)) + stT339o2 343 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 342
    simpa using h
  have hprev := st339o2_p342
  have hstep := st339o2_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p344 : ((1319970246383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 343, stT339o2 (i+1)) + stT339o2 344 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 343
    simpa using h
  have hprev := st339o2_p343
  have hstep := st339o2_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p345 : ((1311153702751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 344, stT339o2 (i+1)) + stT339o2 345 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 344
    simpa using h
  have hprev := st339o2_p344
  have hstep := st339o2_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p346 : ((714981176471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 345, stT339o2 (i+1)) + stT339o2 346 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 345
    simpa using h
  have hprev := st339o2_p345
  have hstep := st339o2_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p347 : ((823910019607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 346, stT339o2 (i+1)) + stT339o2 347 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 346
    simpa using h
  have hprev := st339o2_p346
  have hstep := st339o2_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p348 : ((956680369687/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 347, stT339o2 (i+1)) + stT339o2 348 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 347
    simpa using h
  have hprev := st339o2_p347
  have hstep := st339o2_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p349 : ((4329453929269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 348, stT339o2 (i+1)) + stT339o2 349 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 348
    simpa using h
  have hprev := st339o2_p348
  have hstep := st339o2_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p350 : ((4688035874881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 349, stT339o2 (i+1)) + stT339o2 350 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 349
    simpa using h
  have hprev := st339o2_p349
  have hstep := st339o2_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p351 : ((4821002429761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 350, stT339o2 (i+1)) + stT339o2 351 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 350
    simpa using h
  have hprev := st339o2_p350
  have hstep := st339o2_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p352 : ((4699258376937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 351, stT339o2 (i+1)) + stT339o2 352 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 351
    simpa using h
  have hprev := st339o2_p351
  have hstep := st339o2_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p353 : ((27198693973/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 352, stT339o2 (i+1)) + stT339o2 353 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 352
    simpa using h
  have hprev := st339o2_p352
  have hstep := st339o2_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p354 : ((771638644733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 353, stT339o2 (i+1)) + stT339o2 354 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 353
    simpa using h
  have hprev := st339o2_p353
  have hstep := st339o2_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p355 : ((665994489377/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 354, stT339o2 (i+1)) + stT339o2 355 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 354
    simpa using h
  have hprev := st339o2_p354
  have hstep := st339o2_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p356 : ((45080321503/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 355, stT339o2 (i+1)) + stT339o2 356 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 355
    simpa using h
  have hprev := st339o2_p355
  have hstep := st339o2_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p357 : ((65548050421/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 356, stT339o2 (i+1)) + stT339o2 357 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 356
    simpa using h
  have hprev := st339o2_p356
  have hstep := st339o2_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p358 : ((20292277441/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 357, stT339o2 (i+1)) + stT339o2 358 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 357
    simpa using h
  have hprev := st339o2_p357
  have hstep := st339o2_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p359 : ((2815701434627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 358, stT339o2 (i+1)) + stT339o2 359 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 358
    simpa using h
  have hprev := st339o2_p358
  have hstep := st339o2_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p360 : ((3227855095949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 359, stT339o2 (i+1)) + stT339o2 360 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 359
    simpa using h
  have hprev := st339o2_p359
  have hstep := st339o2_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p361 : ((3743372217409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 360, stT339o2 (i+1)) + stT339o2 361 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 360
    simpa using h
  have hprev := st339o2_p360
  have hstep := st339o2_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p362 : ((4250417998357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 361, stT339o2 (i+1)) + stT339o2 362 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 361
    simpa using h
  have hprev := st339o2_p361
  have hstep := st339o2_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p363 : ((2320085120017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 362, stT339o2 (i+1)) + stT339o2 363 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 362
    simpa using h
  have hprev := st339o2_p362
  have hstep := st339o2_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p364 : ((1207505059499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 363, stT339o2 (i+1)) + stT339o2 364 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 363
    simpa using h
  have hprev := st339o2_p363
  have hstep := st339o2_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p365 : ((1195173059203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 364, stT339o2 (i+1)) + stT339o2 365 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 364
    simpa using h
  have hprev := st339o2_p364
  have hstep := st339o2_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p366 : ((4503859800613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 365, stT339o2 (i+1)) + stT339o2 366 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 365
    simpa using h
  have hprev := st339o2_p365
  have hstep := st339o2_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p367 : ((162355309777/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 366, stT339o2 (i+1)) + stT339o2 367 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 366
    simpa using h
  have hprev := st339o2_p366
  have hstep := st339o2_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p368 : ((3539632934021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 367, stT339o2 (i+1)) + stT339o2 368 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 367
    simpa using h
  have hprev := st339o2_p367
  have hstep := st339o2_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p369 : ((3054437797781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 368, stT339o2 (i+1)) + stT339o2 369 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 368
    simpa using h
  have hprev := st339o2_p368
  have hstep := st339o2_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p370 : ((2703445076009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 369, stT339o2 (i+1)) + stT339o2 370 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 369
    simpa using h
  have hprev := st339o2_p369
  have hstep := st339o2_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p371 : ((2558139415359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 370, stT339o2 (i+1)) + stT339o2 371 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 370
    simpa using h
  have hprev := st339o2_p370
  have hstep := st339o2_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p372 : ((2647181274909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 371, stT339o2 (i+1)) + stT339o2 372 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 371
    simpa using h
  have hprev := st339o2_p371
  have hstep := st339o2_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p373 : ((2951233082069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 372, stT339o2 (i+1)) + stT339o2 373 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 372
    simpa using h
  have hprev := st339o2_p372
  have hstep := st339o2_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p374 : ((681523640993/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 373, stT339o2 (i+1)) + stT339o2 374 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 373
    simpa using h
  have hprev := st339o2_p373
  have hstep := st339o2_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p375 : ((1961820924967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 374, stT339o2 (i+1)) + stT339o2 375 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 374
    simpa using h
  have hprev := st339o2_p374
  have hstep := st339o2_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p376 : ((549451617213/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 375, stT339o2 (i+1)) + stT339o2 376 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 375
    simpa using h
  have hprev := st339o2_p375
  have hstep := st339o2_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p377 : ((94593907363/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 376, stT339o2 (i+1)) + stT339o2 377 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 376
    simpa using h
  have hprev := st339o2_p376
  have hstep := st339o2_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p378 : ((2430177344407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 377, stT339o2 (i+1)) + stT339o2 378 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 377
    simpa using h
  have hprev := st339o2_p377
  have hstep := st339o2_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p379 : ((148838904949/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 378, stT339o2 (i+1)) + stT339o2 379 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 378
    simpa using h
  have hprev := st339o2_p378
  have hstep := st339o2_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p380 : ((139295751979/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 379, stT339o2 (i+1)) + stT339o2 380 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 379
    simpa using h
  have hprev := st339o2_p379
  have hstep := st339o2_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p381 : ((500608336273/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 380, stT339o2 (i+1)) + stT339o2 381 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 380
    simpa using h
  have hprev := st339o2_p380
  have hstep := st339o2_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p382 : ((1746839550407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 381, stT339o2 (i+1)) + stT339o2 382 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 381
    simpa using h
  have hprev := st339o2_p381
  have hstep := st339o2_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p383 : ((3022947160311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 382, stT339o2 (i+1)) + stT339o2 383 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 382
    simpa using h
  have hprev := st339o2_p382
  have hstep := st339o2_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p384 : ((107317567539/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 383, stT339o2 (i+1)) + stT339o2 384 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 383
    simpa using h
  have hprev := st339o2_p383
  have hstep := st339o2_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p385 : ((2538009057771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 384, stT339o2 (i+1)) + stT339o2 385 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 384
    simpa using h
  have hprev := st339o2_p384
  have hstep := st339o2_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p386 : ((2614741242201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 385, stT339o2 (i+1)) + stT339o2 386 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 385
    simpa using h
  have hprev := st339o2_p385
  have hstep := st339o2_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p387 : ((579500043437/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 386, stT339o2 (i+1)) + stT339o2 387 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 386
    simpa using h
  have hprev := st339o2_p386
  have hstep := st339o2_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p388 : ((3332010430463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 387, stT339o2 (i+1)) + stT339o2 388 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 387
    simpa using h
  have hprev := st339o2_p387
  have hstep := st339o2_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p389 : ((3836097319763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 388, stT339o2 (i+1)) + stT339o2 389 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 388
    simpa using h
  have hprev := st339o2_p388
  have hstep := st339o2_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p390 : ((539430112483/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 389, stT339o2 (i+1)) + stT339o2 390 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 389
    simpa using h
  have hprev := st339o2_p389
  have hstep := st339o2_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p391 : ((1170313293443/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 390, stT339o2 (i+1)) + stT339o2 391 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 390
    simpa using h
  have hprev := st339o2_p390
  have hstep := st339o2_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p392 : ((608322399403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 391, stT339o2 (i+1)) + stT339o2 392 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 391
    simpa using h
  have hprev := st339o2_p391
  have hstep := st339o2_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p393 : ((2419136440657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 392, stT339o2 (i+1)) + stT339o2 393 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 392
    simpa using h
  have hprev := st339o2_p392
  have hstep := st339o2_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p394 : ((287659573409/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 393, stT339o2 (i+1)) + stT339o2 394 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 393
    simpa using h
  have hprev := st339o2_p393
  have hstep := st339o2_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p395 : ((4203288109479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 394, stT339o2 (i+1)) + stT339o2 395 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 394
    simpa using h
  have hprev := st339o2_p394
  have hstep := st339o2_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p396 : ((1856745691501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 395, stT339o2 (i+1)) + stT339o2 396 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 395
    simpa using h
  have hprev := st339o2_p395
  have hstep := st339o2_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p397 : ((1610880272163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 396, stT339o2 (i+1)) + stT339o2 397 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 396
    simpa using h
  have hprev := st339o2_p396
  have hstep := st339o2_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p398 : ((2816172567351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 397, stT339o2 (i+1)) + stT339o2 398 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 397
    simpa using h
  have hprev := st339o2_p397
  have hstep := st339o2_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p399 : ((160536498757/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 398, stT339o2 (i+1)) + stT339o2 399 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 398
    simpa using h
  have hprev := st339o2_p398
  have hstep := st339o2_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p400 : ((630532471801/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 399, stT339o2 (i+1)) + stT339o2 400 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 399
    simpa using h
  have hprev := st339o2_p399
  have hstep := st339o2_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p401 : ((671008519573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 400, stT339o2 (i+1)) + stT339o2 401 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 400
    simpa using h
  have hprev := st339o2_p400
  have hstep := st339o2_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p402 : ((1512425071441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 401, stT339o2 (i+1)) + stT339o2 402 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 401
    simpa using h
  have hprev := st339o2_p401
  have hstep := st339o2_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p403 : ((3484162991657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 402, stT339o2 (i+1)) + stT339o2 403 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 402
    simpa using h
  have hprev := st339o2_p402
  have hstep := st339o2_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p404 : ((3981526761077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 403, stT339o2 (i+1)) + stT339o2 404 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 403
    simpa using h
  have hprev := st339o2_p403
  have hstep := st339o2_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p405 : ((2215344405773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 404, stT339o2 (i+1)) + stT339o2 405 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 404
    simpa using h
  have hprev := st339o2_p404
  have hstep := st339o2_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p406 : ((4754527125993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 405, stT339o2 (i+1)) + stT339o2 406 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 405
    simpa using h
  have hprev := st339o2_p405
  have hstep := st339o2_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p407 : ((4898140782123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 406, stT339o2 (i+1)) + stT339o2 407 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 406
    simpa using h
  have hprev := st339o2_p406
  have hstep := st339o2_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p408 : ((4837888296027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 407, stT339o2 (i+1)) + stT339o2 408 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 407
    simpa using h
  have hprev := st339o2_p407
  have hstep := st339o2_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p409 : ((2292479498277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 408, stT339o2 (i+1)) + stT339o2 409 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 408
    simpa using h
  have hprev := st339o2_p408
  have hstep := st339o2_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p410 : ((4182984000049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 409, stT339o2 (i+1)) + stT339o2 410 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 409
    simpa using h
  have hprev := st339o2_p409
  have hstep := st339o2_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p411 : ((3700232442417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 410, stT339o2 (i+1)) + stT339o2 411 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 410
    simpa using h
  have hprev := st339o2_p410
  have hstep := st339o2_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p412 : ((3217842463657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 411, stT339o2 (i+1)) + stT339o2 412 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 411
    simpa using h
  have hprev := st339o2_p411
  have hstep := st339o2_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p413 : ((2816119132593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 412, stT339o2 (i+1)) + stT339o2 413 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 412
    simpa using h
  have hprev := st339o2_p412
  have hstep := st339o2_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p414 : ((2561246613881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 413, stT339o2 (i+1)) + stT339o2 414 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 413
    simpa using h
  have hprev := st339o2_p413
  have hstep := st339o2_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p415 : ((2494568284127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 414, stT339o2 (i+1)) + stT339o2 415 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 414
    simpa using h
  have hprev := st339o2_p414
  have hstep := st339o2_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p416 : ((2626137115337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 415, stT339o2 (i+1)) + stT339o2 416 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 415
    simpa using h
  have hprev := st339o2_p415
  have hstep := st339o2_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p417 : ((2933538731201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 416, stT339o2 (i+1)) + stT339o2 417 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 416
    simpa using h
  have hprev := st339o2_p416
  have hstep := st339o2_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p418 : ((1682984363253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 417, stT339o2 (i+1)) + stT339o2 418 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 417
    simpa using h
  have hprev := st339o2_p417
  have hstep := st339o2_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p419 : ((385286998709/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 418, stT339o2 (i+1)) + stT339o2 419 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 418
    simpa using h
  have hprev := st339o2_p418
  have hstep := st339o2_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p420 : ((431556759869/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 419, stT339o2 (i+1)) + stT339o2 420 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 419
    simpa using h
  have hprev := st339o2_p419
  have hstep := st339o2_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p421 : ((116999975089/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 420, stT339o2 (i+1)) + stT339o2 421 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 420
    simpa using h
  have hprev := st339o2_p420
  have hstep := st339o2_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p422 : ((12221163109/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 421, stT339o2 (i+1)) + stT339o2 422 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 421
    simpa using h
  have hprev := st339o2_p421
  have hstep := st339o2_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p423 : ((30678624997/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 422, stT339o2 (i+1)) + stT339o2 423 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 422
    simpa using h
  have hprev := st339o2_p422
  have hstep := st339o2_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p424 : ((4738017807133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 423, stT339o2 (i+1)) + stT339o2 424 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 423
    simpa using h
  have hprev := st339o2_p423
  have hstep := st339o2_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p425 : ((4404485695437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 424, stT339o2 (i+1)) + stT339o2 425 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 424
    simpa using h
  have hprev := st339o2_p424
  have hstep := st339o2_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p426 : ((3960956576071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 425, stT339o2 (i+1)) + stT339o2 426 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 425
    simpa using h
  have hprev := st339o2_p425
  have hstep := st339o2_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p427 : ((3477067581933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 426, stT339o2 (i+1)) + stT339o2 427 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 426
    simpa using h
  have hprev := st339o2_p426
  have hstep := st339o2_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p428 : ((1514039101029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 427, stT339o2 (i+1)) + stT339o2 428 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 427
    simpa using h
  have hprev := st339o2_p427
  have hstep := st339o2_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p429 : ((2683177277013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 428, stT339o2 (i+1)) + stT339o2 429 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 428
    simpa using h
  have hprev := st339o2_p428
  have hstep := st339o2_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p430 : ((1247456492757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 429, stT339o2 (i+1)) + stT339o2 430 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 429
    simpa using h
  have hprev := st339o2_p429
  have hstep := st339o2_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p431 : ((1245688712477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 430, stT339o2 (i+1)) + stT339o2 431 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 430
    simpa using h
  have hprev := st339o2_p430
  have hstep := st339o2_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p432 : ((2672278981579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 431, stT339o2 (i+1)) + stT339o2 432 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 431
    simpa using h
  have hprev := st339o2_p431
  have hstep := st339o2_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p433 : ((1504677682219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 432, stT339o2 (i+1)) + stT339o2 433 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 432
    simpa using h
  have hprev := st339o2_p432
  have hstep := st339o2_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p434 : ((431376785731/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 433, stT339o2 (i+1)) + stT339o2 434 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 433
    simpa using h
  have hprev := st339o2_p433
  have hstep := st339o2_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p435 : ((3930417352973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 434, stT339o2 (i+1)) + stT339o2 435 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 434
    simpa using h
  have hprev := st339o2_p434
  have hstep := st339o2_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p436 : ((4375680967767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 435, stT339o2 (i+1)) + stT339o2 436 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 435
    simpa using h
  have hprev := st339o2_p435
  have hstep := st339o2_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p437 : ((4720651252911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 436, stT339o2 (i+1)) + stT339o2 437 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 436
    simpa using h
  have hprev := st339o2_p436
  have hstep := st339o2_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p438 : ((4914626726009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 437, stT339o2 (i+1)) + stT339o2 438 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 437
    simpa using h
  have hprev := st339o2_p437
  have hstep := st339o2_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p439 : ((2464826833207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 438, stT339o2 (i+1)) + stT339o2 439 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 438
    simpa using h
  have hprev := st339o2_p438
  have hstep := st339o2_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p440 : ((2382157213819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 439, stT339o2 (i+1)) + stT339o2 440 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 439
    simpa using h
  have hprev := st339o2_p439
  have hstep := st339o2_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p441 : ((4443585979599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 440, stT339o2 (i+1)) + stT339o2 441 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 440
    simpa using h
  have hprev := st339o2_p440
  have hstep := st339o2_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p442 : ((802968841359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 441, stT339o2 (i+1)) + stT339o2 442 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 441
    simpa using h
  have hprev := st339o2_p441
  have hstep := st339o2_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p443 : ((70814130367/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 442, stT339o2 (i+1)) + stT339o2 443 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 442
    simpa using h
  have hprev := st339o2_p442
  have hstep := st339o2_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p444 : ((3089789552711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 443, stT339o2 (i+1)) + stT339o2 444 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 443
    simpa using h
  have hprev := st339o2_p443
  have hstep := st339o2_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p445 : ((2726766074003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 444, stT339o2 (i+1)) + stT339o2 445 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 444
    simpa using h
  have hprev := st339o2_p444
  have hstep := st339o2_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p446 : ((2503173236717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 445, stT339o2 (i+1)) + stT339o2 446 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 445
    simpa using h
  have hprev := st339o2_p445
  have hstep := st339o2_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p447 : ((2450231664613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 446, stT339o2 (i+1)) + stT339o2 447 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 446
    simpa using h
  have hprev := st339o2_p446
  have hstep := st339o2_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p448 : ((1287353983049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 447, stT339o2 (i+1)) + stT339o2 448 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 447
    simpa using h
  have hprev := st339o2_p447
  have hstep := st339o2_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p449 : ((1429125230081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 448, stT339o2 (i+1)) + stT339o2 449 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 448
    simpa using h
  have hprev := st339o2_p448
  have hstep := st339o2_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p450 : ((1630162772643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 449, stT339o2 (i+1)) + stT339o2 450 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 449
    simpa using h
  have hprev := st339o2_p449
  have hstep := st339o2_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p451 : ((3724164519931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 450, stT339o2 (i+1)) + stT339o2 451 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 450
    simpa using h
  have hprev := st339o2_p450
  have hstep := st339o2_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p452 : ((4184886373171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 451, stT339o2 (i+1)) + stT339o2 452 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 451
    simpa using h
  have hprev := st339o2_p451
  have hstep := st339o2_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p453 : ((4578602896371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 452, stT339o2 (i+1)) + stT339o2 453 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 452
    simpa using h
  have hprev := st339o2_p452
  have hstep := st339o2_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p454 : ((4851240136239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 453, stT339o2 (i+1)) + stT339o2 454 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 453
    simpa using h
  have hprev := st339o2_p453
  have hstep := st339o2_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p455 : ((4965822192723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 454, stT339o2 (i+1)) + stT339o2 455 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 454
    simpa using h
  have hprev := st339o2_p454
  have hstep := st339o2_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p456 : ((4907341762883/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 455, stT339o2 (i+1)) + stT339o2 456 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 455
    simpa using h
  have hprev := st339o2_p455
  have hstep := st339o2_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p457 : ((468451288019/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 456, stT339o2 (i+1)) + stT339o2 457 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 456
    simpa using h
  have hprev := st339o2_p456
  have hstep := st339o2_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p458 : ((108206644123/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 457, stT339o2 (i+1)) + stT339o2 458 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 457
    simpa using h
  have hprev := st339o2_p457
  have hstep := st339o2_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p459 : ((485912480603/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 458, stT339o2 (i+1)) + stT339o2 459 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 458
    simpa using h
  have hprev := st339o2_p458
  have hstep := st339o2_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p460 : ((21383151353/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 459, stT339o2 (i+1)) + stT339o2 460 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 459
    simpa using h
  have hprev := st339o2_p459
  have hstep := st339o2_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p461 : ((2992807195793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 460, stT339o2 (i+1)) + stT339o2 461 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 460
    simpa using h
  have hprev := st339o2_p460
  have hstep := st339o2_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p462 : ((531760360441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 461, stT339o2 (i+1)) + stT339o2 462 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 461
    simpa using h
  have hprev := st339o2_p461
  have hstep := st339o2_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p463 : ((492650537533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 462, stT339o2 (i+1)) + stT339o2 463 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 462
    simpa using h
  have hprev := st339o2_p462
  have hstep := st339o2_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p464 : ((486286749321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 463, stT339o2 (i+1)) + stT339o2 464 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 463
    simpa using h
  have hprev := st339o2_p463
  have hstep := st339o2_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p465 : ((2566846633819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 464, stT339o2 (i+1)) + stT339o2 465 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 464
    simpa using h
  have hprev := st339o2_p464
  have hstep := st339o2_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p466 : ((570204920943/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 465, stT339o2 (i+1)) + stT339o2 466 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 465
    simpa using h
  have hprev := st339o2_p465
  have hstep := st339o2_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p467 : ((3246234819867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 466, stT339o2 (i+1)) + stT339o2 467 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 466
    simpa using h
  have hprev := st339o2_p466
  have hstep := st339o2_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p468 : ((3700624720867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 467, stT339o2 (i+1)) + stT339o2 468 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 467
    simpa using h
  have hprev := st339o2_p467
  have hstep := st339o2_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p469 : ((129847258763/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 468, stT339o2 (i+1)) + stT339o2 469 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 468
    simpa using h
  have hprev := st339o2_p468
  have hstep := st339o2_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p470 : ((4551095828761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 469, stT339o2 (i+1)) + stT339o2 470 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 469
    simpa using h
  have hprev := st339o2_p469
  have hstep := st339o2_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p471 : ((4837975265311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 470, stT339o2 (i+1)) + stT339o2 471 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 470
    simpa using h
  have hprev := st339o2_p470
  have hstep := st339o2_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p472 : ((497952134269/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 471, stT339o2 (i+1)) + stT339o2 472 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 471
    simpa using h
  have hprev := st339o2_p471
  have hstep := st339o2_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p473 : ((2479155821081/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 472, stT339o2 (i+1)) + stT339o2 473 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 472
    simpa using h
  have hprev := st339o2_p472
  have hstep := st339o2_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p474 : ((477769848601/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 473, stT339o2 (i+1)) + stT339o2 474 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 473
    simpa using h
  have hprev := st339o2_p473
  have hstep := st339o2_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p475 : ((2230572162197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 474, stT339o2 (i+1)) + stT339o2 475 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 474
    simpa using h
  have hprev := st339o2_p474
  have hstep := st339o2_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p476 : ((126531540517/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 475, stT339o2 (i+1)) + stT339o2 476 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 475
    simpa using h
  have hprev := st339o2_p475
  have hstep := st339o2_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p477 : ((1796642019601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 476, stT339o2 (i+1)) + stT339o2 477 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 476
    simpa using h
  have hprev := st339o2_p476
  have hstep := st339o2_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p478 : ((196935629437/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 477, stT339o2 (i+1)) + stT339o2 478 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 477
    simpa using h
  have hprev := st339o2_p477
  have hstep := st339o2_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p479 : ((173558298097/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 478, stT339o2 (i+1)) + stT339o2 479 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 478
    simpa using h
  have hprev := st339o2_p478
  have hstep := st339o2_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p480 : ((125857679473/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 479, stT339o2 (i+1)) + stT339o2 480 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 479
    simpa using h
  have hprev := st339o2_p479
  have hstep := st339o2_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p481 : ((600787187177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 480, stT339o2 (i+1)) + stT339o2 481 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 480
    simpa using h
  have hprev := st339o2_p480
  have hstep := st339o2_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p482 : ((612078709907/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 481, stT339o2 (i+1)) + stT339o2 482 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 481
    simpa using h
  have hprev := st339o2_p481
  have hstep := st339o2_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p483 : ((661619833077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 482, stT339o2 (i+1)) + stT339o2 483 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 482
    simpa using h
  have hprev := st339o2_p482
  have hstep := st339o2_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p484 : ((2972919460413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 483, stT339o2 (i+1)) + stT339o2 484 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 483
    simpa using h
  have hprev := st339o2_p483
  have hstep := st339o2_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p485 : ((3387558959813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 484, stT339o2 (i+1)) + stT339o2 485 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 484
    simpa using h
  have hprev := st339o2_p484
  have hstep := st339o2_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p486 : ((3840015792953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 485, stT339o2 (i+1)) + stT339o2 486 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 485
    simpa using h
  have hprev := st339o2_p485
  have hstep := st339o2_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p487 : ((4275760820611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 486, stT339o2 (i+1)) + stT339o2 487 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 486
    simpa using h
  have hprev := st339o2_p486
  have hstep := st339o2_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p488 : ((185708299689/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 487, stT339o2 (i+1)) + stT339o2 488 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 487
    simpa using h
  have hprev := st339o2_p487
  have hstep := st339o2_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p489 : ((489739633687/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 488, stT339o2 (i+1)) + stT339o2 489 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 488
    simpa using h
  have hprev := st339o2_p488
  have hstep := st339o2_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p490 : ((2505017311439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 489, stT339o2 (i+1)) + stT339o2 490 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 489
    simpa using h
  have hprev := st339o2_p489
  have hstep := st339o2_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p491 : ((620982931881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 490, stT339o2 (i+1)) + stT339o2 491 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 490
    simpa using h
  have hprev := st339o2_p490
  have hstep := st339o2_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p492 : ((4776467316653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 491, stT339o2 (i+1)) + stT339o2 492 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 491
    simpa using h
  have hprev := st339o2_p491
  have hstep := st339o2_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p493 : ((4458888224111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 492, stT339o2 (i+1)) + stT339o2 493 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 492
    simpa using h
  have hprev := st339o2_p492
  have hstep := st339o2_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p494 : ((810543507847/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 493, stT339o2 (i+1)) + stT339o2 494 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 493
    simpa using h
  have hprev := st339o2_p493
  have hstep := st339o2_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p495 : ((1802782422409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 494, stT339o2 (i+1)) + stT339o2 495 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 494
    simpa using h
  have hprev := st339o2_p494
  have hstep := st339o2_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p496 : ((1584703057819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 495, stT339o2 (i+1)) + stT339o2 496 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 495
    simpa using h
  have hprev := st339o2_p495
  have hstep := st339o2_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p497 : ((139726940759/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 496, stT339o2 (i+1)) + stT339o2 497 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 496
    simpa using h
  have hprev := st339o2_p496
  have hstep := st339o2_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p498 : ((2523812106419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 497, stT339o2 (i+1)) + stT339o2 498 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 497
    simpa using h
  have hprev := st339o2_p497
  have hstep := st339o2_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p499 : ((2387815076791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 498, stT339o2 (i+1)) + stT339o2 499 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 498
    simpa using h
  have hprev := st339o2_p498
  have hstep := st339o2_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_p500 : ((2401528416223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT339o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT339o2 (i+1))
      = (∑ i ∈ Finset.range 499, stT339o2 (i+1)) + stT339o2 500 := by
    have h := Finset.sum_range_succ (fun i => stT339o2 (i+1)) 499
    simpa using h
  have hprev := st339o2_p499
  have hstep := st339o2_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st339o2_s500 :
    |Real.sin (((339 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))
      - ((-124941/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((388413/125000 : ℚ) : ℝ) ≤ Real.log ((500 : ℕ)) / 2 := by
    have h := (log_br_500).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((500 : ℕ)) / 2 ≤ ((62146081/20000000 : ℚ) : ℝ) := by
    have h := (log_br_500).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := -3850193/10000000) (δ := 1709/200000000) (ψ := -65899/100000) 339 168
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 339/2`** (evaluated boundary). -/
theorem station_339o2_sign : 0 < hardyG (((((339:ℕ)):ℝ)/2)) := by
  have hcore := phase_station_lower_half_eval 339 500 (by norm_num) (by norm_num)
    ((-65899/100000 : ℚ) : ℝ)
  have hchain := st339o2_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT339o2 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((339 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((-65899/100000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st339o2_c500
  have hsinb := abs_le.mp st339o2_s500
  have hbdy_lo : ((75756155510607/574610000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((339 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ))) / 2
          - ((((339:ℕ)):ℝ)/2)
            * Real.sin (((339 : ℕ) : ℝ) * (Real.log ((500 : ℕ)) / 2) - ((-65899/100000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((339:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((339:ℝ) * (Real.log (500:ℝ) / 2) - ((-65899/100000 : ℚ) : ℝ))) / 2
        - ((339:ℝ)/2) * Real.sin ((339:ℝ) * (Real.log (500:ℝ) / 2) - ((-65899/100000 : ℚ) : ℝ))
        ≥ ((169396139/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((339:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((169396139/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((169396139/1000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((169396139/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((339:ℕ)):ℝ)/2)+1) * (((((339:ℕ)):ℝ)/2)+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((28915490777623/120000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2401528416223/10000000000000 : ℚ) : ℝ) + ((75756155510607/574610000000000 : ℚ) : ℝ)
      - ((28915490777623/120000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-65899/100000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((339:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-65899/100000 : ℚ) : ℝ)
        * (riemannZeta (line (((((339:ℕ)):ℝ)/2)))).re
      - Real.sin ((-65899/100000 : ℚ) : ℝ)
        * (riemannZeta (line (((((339:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((339:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((339:ℕ)):ℝ)/2))
      = ((((((339:ℕ)):ℝ)/2)) * (Real.log (((((339:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((339:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((51328529/10000000 : ℚ) : ℝ) ≤ Real.log (((((339:ℕ)):ℝ)/2))
      ∧ Real.log (((((339:ℕ)):ℝ)/2)) ≤ ((51328531/10000000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((339:ℕ)):ℝ)/2))
        = Real.log ((((339:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_339
    have h2 := log_br_2
    rw [hsplit]
    push_cast at hM h2 ⊢
    constructor <;> linarith [hM.1, hM.2, h2.1, h2.2]
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
  have hθwin : |(((-65899/100000 : ℚ) : ℝ) + ((31:ℤ)) * (2*Real.pi)) - theta (((((339:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((339:ℕ)):ℝ)/2)))
    (φ := ((-65899/100000 : ℚ) : ℝ) + ((31:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-65899/100000 : ℚ)) : ℝ) 31).1,
    (cos_sin_shift (((-65899/100000 : ℚ)) : ℝ) 31).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_339o2_sign
end AxiomAudit
