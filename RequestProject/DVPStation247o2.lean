import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationHalfEval

/-!
# Station `t = 247/2` (rung-126; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT247o2 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((247 : ℕ) : ℝ) * (Real.log ((n : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))

theorem st247o2_c1 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((365619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((0 : ℚ) : ℝ) ≤ Real.log ((1 : ℕ)) / 2 := by
    have h := (log_br_1).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((1 : ℕ)) / 2 ≤ ((0 : ℚ) : ℝ) := by
    have h := (log_br_1).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 469163/2500000) (δ := 21/100000000) (ψ := -750661/1000000) 247 0
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t1 : ((182797/250000 : ℚ) : ℝ) ≤ stT247o2 1 := by
  have hc : ((182797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((1 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182797/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((182797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c2 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-789/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6931471/20000000 : ℚ) : ℝ) ≤ Real.log ((2 : ℕ)) / 2 := by
    have h := (log_br_2).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((2 : ℕ)) / 2 ≤ ((433217/1250000 : ℚ) : ℝ) := by
    have h := (log_br_2).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2012821/5000000) (δ := 967/100000000) (ψ := -750661/1000000) 247 14
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t2 : ((-139653593/5000000000 : ℚ) : ℝ) ≤ stT247o2 2 := by
  have hc : ((-79/2000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((2 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139653593/5000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-79/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c3 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-11399/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5493061/10000000 : ℚ) : ℝ) ≤ Real.log ((3 : ℕ)) / 2 := by
    have h := (log_br_3).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((3 : ℕ)) / 2 ≤ ((10986123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_3).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1125499/2500000) (δ := 1067/100000000) (ψ := -750661/1000000) 247 22
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t3 : ((-131653188909/1000000000000 : ℚ) : ℝ) ≤ stT247o2 3 := by
  have hc : ((-22803/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((3 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131653188909/1000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-22803/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c4 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-135037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13862943/20000000 : ℚ) : ℝ) ≤ Real.log ((4 : ℕ)) / 2 := by
    have h := (log_br_4).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((4 : ℕ)) / 2 ≤ ((433217/625000 : ℚ) : ℝ) := by
    have h := (log_br_4).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1445007/2500000) (δ := 373/50000000) (ψ := -750661/1000000) 247 27
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t4 : ((-675235135047/2000000000000 : ℚ) : ℝ) ≤ stT247o2 4 := by
  have hc : ((-135047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((4 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675235135047/2000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-135047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c5 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((25107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/20000000 : ℚ) : ℝ) ≤ Real.log ((5 : ℕ)) / 2 := by
    have h := (log_br_5).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((5 : ℕ)) / 2 ≤ ((804719/1000000 : ℚ) : ℝ) := by
    have h := (log_br_5).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3864217/10000000) (δ := 1099/100000000) (ψ := -750661/1000000) 247 32
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t5 : ((22411657339/2000000000000 : ℚ) : ℝ) ≤ stT247o2 5 := by
  have hc : ((25057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((5 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22411657339/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((25057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c6 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-523261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8958797/10000000 : ℚ) : ℝ) ≤ Real.log ((6 : ℕ)) / 2 := by
    have h := (log_br_6).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((6 : ℕ)) / 2 ≤ ((3583519/4000000 : ℚ) : ℝ) := by
    have h := (log_br_6).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2651837/5000000) (δ := 847/100000000) (ψ := -750661/1000000) 247 35
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t6 : ((-2136408261213/10000000000000 : ℚ) : ℝ) ≤ stT247o2 6 := by
  have hc : ((-523311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((6 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2136408261213/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-523311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c7 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-673347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/20000000 : ℚ) : ℝ) ≤ Real.log ((7 : ℕ)) / 2 := by
    have h := (log_br_7).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((7 : ℕ)) / 2 ≤ ((9729551/10000000 : ℚ) : ℝ) := by
    have h := (log_br_7).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2886903/5000000) (δ := 83/12500000) (ψ := -750661/1000000) 247 38
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t7 : ((-509040320813/2000000000000 : ℚ) : ℝ) ≤ stT247o2 7 := by
  have hc : ((-673397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((7 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-509040320813/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-673397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c8 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((249701/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/4000000 : ℚ) : ℝ) ≤ Real.log ((8 : ℕ)) / 2 := by
    have h := (log_br_8).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((8 : ℕ)) / 2 ≤ ((1299651/1250000 : ℚ) : ℝ) := by
    have h := (log_br_8).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -61133/5000000) (δ := 371/50000000) (ψ := -750661/1000000) 247 41
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t8 : ((1765563862941/5000000000000 : ℚ) : ℝ) ≤ stT247o2 8 := by
  have hc : ((499377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((8 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1765563862941/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((499377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c9 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-352397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4394449/4000000 : ℚ) : ℝ) ≤ Real.log ((9 : ℕ)) / 2 := by
    have h := (log_br_9).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((9 : ℕ)) / 2 ≤ ((10986123/10000000 : ℚ) : ℝ) := by
    have h := (log_br_9).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 120683/250000) (δ := 947/100000000) (ψ := -750661/1000000) 247 43
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t9 : ((-587411784149/5000000000000 : ℚ) : ℝ) ≤ stT247o2 9 := by
  have hc : ((-352447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((9 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-587411784149/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-352447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c10 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-360687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((460517/400000 : ℚ) : ℝ) ≤ Real.log ((10 : ℕ)) / 2 := by
    have h := (log_br_10).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((10 : ℕ)) / 2 ≤ ((23025851/20000000 : ℚ) : ℝ) := by
    have h := (log_br_10).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1485363/2500000) (δ := 557/50000000) (ψ := -750661/1000000) 247 45
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t10 : ((-71291976371/312500000000 : ℚ) : ℝ) ≤ stT247o2 10 := by
  have hc : ((-45089/62500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((10 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71291976371/312500000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-45089/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c11 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-10221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2997369/2500000 : ℚ) : ℝ) ≤ Real.log ((11 : ℕ)) / 2 := by
    have h := (log_br_11).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((11 : ℕ)) / 2 ≤ ((23978953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_11).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 123517/312500) (δ := 177/20000000) (ψ := -750661/1000000) 247 47
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t11 : ((-15484117947/5000000000000 : ℚ) : ℝ) ≤ stT247o2 11 := by
  have hc : ((-10271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((11 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15484117947/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-10271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c12 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((971469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/10000000 : ℚ) : ℝ) ≤ Real.log ((12 : ℕ)) / 2 := by
    have h := (log_br_12).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((12 : ℕ)) / 2 ≤ ((24849067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_12).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -29931/500000) (δ := 641/100000000) (ψ := -750661/1000000) 247 49
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t12 : ((2804244769669/10000000000000 : ℚ) : ℝ) ≤ stT247o2 12 := by
  have hc : ((971419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((12 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2804244769669/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((971419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c13 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-243917/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25649493/20000000 : ℚ) : ℝ) ≤ Real.log ((13 : ℕ)) / 2 := by
    have h := (log_br_13).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((13 : ℕ)) / 2 ≤ ((12824747/10000000 : ℚ) : ℝ) := by
    have h := (log_br_13).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7301361/10000000) (δ := 673/100000000) (ψ := -750661/1000000) 247 51
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t13 : ((-1353077424359/5000000000000 : ℚ) : ℝ) ≤ stT247o2 13 := by
  have hc : ((-487859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((13 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1353077424359/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-487859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c14 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((24967/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/20000000 : ℚ) : ℝ) ≤ Real.log ((14 : ℕ)) / 2 := by
    have h := (log_br_14).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((14 : ℕ)) / 2 ≤ ((13195287/10000000 : ℚ) : ℝ) := by
    have h := (log_br_14).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -128487/10000000) (δ := 437/50000000) (ψ := -750661/1000000) 247 52
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t14 : ((66723763039/250000000000 : ℚ) : ℝ) ≤ stT247o2 14 := by
  have hc : ((99863/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((14 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66723763039/250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((99863/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c15 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-577157/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/10000000 : ℚ) : ℝ) ≤ Real.log ((15 : ℕ)) / 2 := by
    have h := (log_br_15).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((15 : ℕ)) / 2 ≤ ((27080503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_15).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2732549/5000000) (δ := 629/50000000) (ψ := -750661/1000000) 247 53
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t15 : ((-1490342124723/10000000000000 : ℚ) : ℝ) ≤ stT247o2 15 := by
  have hc : ((-577207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((15 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1490342124723/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-577207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c16 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-371997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27725887/20000000 : ℚ) : ℝ) ≤ Real.log ((16 : ℕ)) / 2 := by
    have h := (log_br_16).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((16 : ℕ)) / 2 ≤ ((433217/312500 : ℚ) : ℝ) := by
    have h := (log_br_16).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -75307/125000) (δ := 31/3125000) (ψ := -750661/1000000) 247 55
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t16 : ((-465027686011/2500000000000 : ℚ) : ℝ) ≤ stT247o2 16 := by
  have hc : ((-186011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((16 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-465027686011/2500000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-186011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c17 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((178441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28332133/20000000 : ℚ) : ℝ) ≤ Real.log ((17 : ℕ)) / 2 := by
    have h := (log_br_17).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((17 : ℕ)) / 2 ≤ ((14166067/10000000 : ℚ) : ℝ) := by
    have h := (log_br_17).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3014671/10000000) (δ := 711/100000000) (ψ := -750661/1000000) 247 56
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t17 : ((6761286189/78125000000 : ℚ) : ℝ) ≤ stT247o2 17 := by
  have hc : ((11151/31250 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((17 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6761286189/78125000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((11151/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c18 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((90897/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((28903717/20000000 : ℚ) : ℝ) ≤ Real.log ((18 : ℕ)) / 2 := by
    have h := (log_br_18).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((18 : ℕ)) / 2 ≤ ((14451859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_18).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -537487/5000000) (δ := 697/100000000) (ψ := -750661/1000000) 247 57
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t18 : ((26779305453/125000000000 : ℚ) : ℝ) ≤ stT247o2 18 := by
  have hc : ((22723/25000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((18 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26779305453/125000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((22723/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c19 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((999357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((29444389/20000000 : ℚ) : ℝ) ≤ Real.log ((19 : ℕ)) / 2 := by
    have h := (log_br_19).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((19 : ℕ)) / 2 ≤ ((2944439/2000000 : ℚ) : ℝ) := by
    have h := (log_br_19).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -89683/10000000) (δ := 237/25000000) (ψ := -750661/1000000) 247 58
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t19 : ((2292567149199/10000000000000 : ℚ) : ℝ) ≤ stT247o2 19 := by
  have hc : ((999307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((19 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2292567149199/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((999307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c20 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((999877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((14978661/10000000 : ℚ) : ℝ) ≤ Real.log ((20 : ℕ)) / 2 := by
    have h := (log_br_20).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((20 : ℕ)) / 2 ≤ ((29957323/20000000 : ℚ) : ℝ) := by
    have h := (log_br_20).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 39159/10000000) (δ := 113/12500000) (ψ := -750661/1000000) 247 59
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t20 : ((2235680160409/10000000000000 : ℚ) : ℝ) ≤ stT247o2 20 := by
  have hc : ((999827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((20 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2235680160409/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((999827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c21 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((242719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3805653/2500000 : ℚ) : ℝ) ≤ Real.log ((21 : ℕ)) / 2 := by
    have h := (log_br_21).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((21 : ℕ)) / 2 ≤ ((1217809/800000 : ℚ) : ℝ) := by
    have h := (log_br_21).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -604841/10000000) (δ := 773/100000000) (ψ := -750661/1000000) 247 60
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t21 : ((529628784757/2500000000000 : ℚ) : ℝ) ≤ stT247o2 21 := by
  have hc : ((485413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((21 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((529628784757/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((485413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c22 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((88873/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3863803/2500000 : ℚ) : ℝ) ≤ Real.log ((22 : ℕ)) / 2 := by
    have h := (log_br_22).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((22 : ℕ)) / 2 ≤ ((1236417/800000 : ℚ) : ℝ) := by
    have h := (log_br_22).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7799/40000) (δ := 127/20000000) (ψ := -750661/1000000) 247 61
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t22 : ((757858132269/5000000000000 : ℚ) : ℝ) ≤ stT247o2 22 := by
  have hc : ((355467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((22 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((757858132269/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((355467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c23 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-39/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15677471/10000000 : ℚ) : ℝ) ≤ Real.log ((23 : ℕ)) / 2 := by
    have h := (log_br_23).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((23 : ℕ)) / 2 ≤ ((31354943/20000000 : ℚ) : ℝ) := by
    have h := (log_br_23).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3933231/10000000) (δ := 521/50000000) (ψ := -750661/1000000) 247 62
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t23 : ((-530877917/1000000000000 : ℚ) : ℝ) ≤ stT247o2 23 := by
  have hc : ((-1273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((23 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530877917/1000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-1273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c24 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-857077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((15890269/10000000 : ℚ) : ℝ) ≤ Real.log ((24 : ℕ)) / 2 := by
    have h := (log_br_24).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((24 : ℕ)) / 2 ≤ ((31780539/20000000 : ℚ) : ℝ) := by
    have h := (log_br_24).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3250457/5000000) (δ := 891/100000000) (ψ := -750661/1000000) 247 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t24 : ((-874801815867/5000000000000 : ℚ) : ℝ) ≤ stT247o2 24 := by
  have hc : ((-857127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((24 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-874801815867/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-857127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c25 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-764557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16094379/10000000 : ℚ) : ℝ) ≤ Real.log ((25 : ℕ)) / 2 := by
    have h := (log_br_25).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((25 : ℕ)) / 2 ≤ ((32188759/20000000 : ℚ) : ℝ) := by
    have h := (log_br_25).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6102877/10000000) (δ := 951/100000000) (ψ := -750661/1000000) 247 63
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t25 : ((-1529214764607/10000000000000 : ℚ) : ℝ) ≤ stT247o2 25 := by
  have hc : ((-764607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((25 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1529214764607/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-764607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c26 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((538851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6516193/4000000 : ℚ) : ℝ) ≤ Real.log ((26 : ℕ)) / 2 := by
    have h := (log_br_26).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((26 : ℕ)) / 2 ≤ ((16290483/10000000 : ℚ) : ℝ) := by
    have h := (log_br_26).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2504309/10000000) (δ := 393/50000000) (ψ := -750661/1000000) 247 64
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t26 : ((1056675507961/10000000000000 : ℚ) : ℝ) ≤ stT247o2 26 := by
  have hc : ((538801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((26 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1056675507961/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((538801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c27 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((81357/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1029949/625000 : ℚ) : ℝ) ≤ Real.log ((27 : ℕ)) / 2 := by
    have h := (log_br_27).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((27 : ℕ)) / 2 ≤ ((32958369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_27).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -48479/312500) (δ := 399/50000000) (ψ := -750661/1000000) 247 65
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t27 : ((39140481/250000000 : ℚ) : ℝ) ≤ stT247o2 27 := by
  have hc : ((10169/12500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((27 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39140481/250000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((10169/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c28 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-372827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6664409/4000000 : ℚ) : ℝ) ≤ Real.log ((28 : ℕ)) / 2 := by
    have h := (log_br_28).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((28 : ℕ)) / 2 ≤ ((16661023/10000000 : ℚ) : ℝ) := by
    have h := (log_br_28).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6030781/10000000) (δ := 281/25000000) (ψ := -750661/1000000) 247 66
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t28 : ((-176156071299/1250000000000 : ℚ) : ℝ) ≤ stT247o2 28 := by
  have hc : ((-93213/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((28 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176156071299/1250000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-93213/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c29 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-171763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((16836479/10000000 : ℚ) : ℝ) ≤ Real.log ((29 : ℕ)) / 2 := by
    have h := (log_br_29).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((29 : ℕ)) / 2 ≤ ((33672959/20000000 : ℚ) : ℝ) := by
    have h := (log_br_29).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 300229/625000) (δ := 879/100000000) (ψ := -750661/1000000) 247 66
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t29 : ((-39875301719/625000000000 : ℚ) : ℝ) ≤ stT247o2 29 := by
  have hc : ((-42947/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((29 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39875301719/625000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-42947/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c30 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((246187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34011973/20000000 : ℚ) : ℝ) ≤ Real.log ((30 : ℕ)) / 2 := by
    have h := (log_br_30).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((30 : ℕ)) / 2 ≤ ((17005987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_30).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -87439/2000000) (δ := 201/20000000) (ψ := -750661/1000000) 247 67
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t30 : ((898901755609/5000000000000 : ℚ) : ℝ) ≤ stT247o2 30 := by
  have hc : ((492349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((30 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((898901755609/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((492349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c31 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-371561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1073121/625000 : ℚ) : ℝ) ≤ Real.log ((31 : ℕ)) / 2 := by
    have h := (log_br_31).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((31 : ℕ)) / 2 ≤ ((34339873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_31).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6021301/10000000) (δ := 151/12500000) (ψ := -750661/1000000) 247 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t31 : ((-166847130411/1250000000000 : ℚ) : ℝ) ≤ stT247o2 31 := by
  have hc : ((-185793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((31 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166847130411/1250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-185793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c32 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((58319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((34657359/20000000 : ℚ) : ℝ) ≤ Real.log ((32 : ℕ)) / 2 := by
    have h := (log_br_32).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((32 : ℕ)) / 2 ≤ ((433217/250000 : ℚ) : ℝ) := by
    have h := (log_br_32).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 378111/1000000) (δ := 1213/100000000) (ψ := -750661/1000000) 247 68
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t32 : ((51502978527/5000000000000 : ℚ) : ℝ) ≤ stT247o2 32 := by
  have hc : ((58269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((32 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51502978527/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((58269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c33 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((112987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1398603/800000 : ℚ) : ℝ) ≤ Real.log ((33 : ℕ)) / 2 := by
    have h := (log_br_33).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((33 : ℕ)) / 2 ≤ ((8741269/5000000 : ℚ) : ℝ) := by
    have h := (log_br_33).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -303263/1250000) (δ := 23/3125000) (ψ := -750661/1000000) 247 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t33 : ((24583456269/250000000000 : ℚ) : ℝ) ≤ stT247o2 33 := by
  have hc : ((112977/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((33 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24583456269/250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((112977/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c34 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-910959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((7052721/4000000 : ℚ) : ℝ) ≤ Real.log ((34 : ℕ)) / 2 := by
    have h := (log_br_34).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((34 : ℕ)) / 2 ≤ ((17631803/10000000 : ℚ) : ℝ) := by
    have h := (log_br_34).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3395499/5000000) (δ := 243/25000000) (ψ := -750661/1000000) 247 69
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t34 : ((-781183840437/5000000000000 : ℚ) : ℝ) ≤ stT247o2 34 := by
  have hc : ((-911009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((34 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-781183840437/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-911009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c35 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((999913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((888837/500000 : ℚ) : ℝ) ≤ Real.log ((35 : ℕ)) / 2 := by
    have h := (log_br_35).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((35 : ℕ)) / 2 ≤ ((35553481/20000000 : ℚ) : ℝ) := by
    have h := (log_br_35).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 32937/10000000) (δ := 183/25000000) (ψ := -750661/1000000) 247 70
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t35 : ((422519106951/2500000000000 : ℚ) : ℝ) ≤ stT247o2 35 := by
  have hc : ((999863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((35 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422519106951/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((999863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c36 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-939137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((35835189/20000000 : ℚ) : ℝ) ≤ Real.log ((36 : ℕ)) / 2 := by
    have h := (log_br_36).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((36 : ℕ)) / 2 ≤ ((3583519/2000000 : ℚ) : ℝ) := by
    have h := (log_br_36).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1744317/2500000) (δ := 791/100000000) (ψ := -750661/1000000) 247 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t36 : ((-1565311979729/10000000000000 : ℚ) : ℝ) ≤ stT247o2 36 := by
  have hc : ((-939187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((36 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1565311979729/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-939187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c37 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((829343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36109179/20000000 : ℚ) : ℝ) ≤ Real.log ((37 : ℕ)) / 2 := by
    have h := (log_br_37).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((37 : ℕ)) / 2 ≤ ((1805459/1000000 : ℚ) : ℝ) := by
    have h := (log_br_37).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 741083/5000000) (δ := 1081/100000000) (ψ := -750661/1000000) 247 71
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t37 : ((1363348569777/10000000000000 : ℚ) : ℝ) ≤ stT247o2 37 := by
  have hc : ((829293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((37 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1363348569777/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((829293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c38 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-367611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((36375861/20000000 : ℚ) : ℝ) ≤ Real.log ((38 : ℕ)) / 2 := by
    have h := (log_br_38).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((38 : ℕ)) / 2 ≤ ((18187931/10000000 : ℚ) : ℝ) := by
    have h := (log_br_38).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -748997/1250000) (δ := 369/50000000) (ψ := -750661/1000000) 247 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t38 : ((-29819231687/250000000000 : ℚ) : ℝ) ≤ stT247o2 38 := by
  have hc : ((-91909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((38 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29819231687/250000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-91909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c39 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((344321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1144863/625000 : ℚ) : ℝ) ≤ Real.log ((39 : ℕ)) / 2 := by
    have h := (log_br_39).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((39 : ℕ)) / 2 ≤ ((36635617/20000000 : ℚ) : ℝ) := by
    have h := (log_br_39).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 405591/2000000) (δ := 137/20000000) (ψ := -750661/1000000) 247 72
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t39 : ((68914330397/625000000000 : ℚ) : ℝ) ≤ stT247o2 39 := by
  have hc : ((43037/62500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((39 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68914330397/625000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((43037/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c40 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-699329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((18444397/10000000 : ℚ) : ℝ) ≤ Real.log ((40 : ℕ)) / 2 := by
    have h := (log_br_40).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((40 : ℕ)) / 2 ≤ ((7377759/4000000 : ℚ) : ℝ) := by
    have h := (log_br_40).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1172627/2000000) (δ := 327/50000000) (ψ := -750661/1000000) 247 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t40 : ((-1105815412681/10000000000000 : ℚ) : ℝ) ≤ stT247o2 40 := by
  have hc : ((-699379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((40 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1105815412681/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-699379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c41 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((190519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((928393/500000 : ℚ) : ℝ) ≤ Real.log ((41 : ℕ)) / 2 := by
    have h := (log_br_41).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((41 : ℕ)) / 2 ≤ ((37135721/20000000 : ℚ) : ℝ) := by
    have h := (log_br_41).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1760709/10000000) (δ := 201/25000000) (ψ := -750661/1000000) 247 73
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t41 : ((595042099581/5000000000000 : ℚ) : ℝ) ≤ stT247o2 41 := by
  have hc : ((381013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((41 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((595042099581/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((381013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c42 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-858357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4672087/2500000 : ℚ) : ℝ) ≤ Real.log ((42 : ℕ)) / 2 := by
    have h := (log_br_42).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((42 : ℕ)) / 2 ≤ ((37376697/20000000 : ℚ) : ℝ) := by
    have h := (log_br_42).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1301427/2000000) (δ := 1023/100000000) (ψ := -750661/1000000) 247 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t42 : ((-662275593419/5000000000000 : ℚ) : ℝ) ≤ stT247o2 42 := by
  have hc : ((-858407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((42 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-662275593419/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-858407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c43 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((954397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((37612001/20000000 : ℚ) : ℝ) ≤ Real.log ((43 : ℕ)) / 2 := by
    have h := (log_br_43).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((43 : ℕ)) / 2 ≤ ((18806001/10000000 : ℚ) : ℝ) := by
    have h := (log_br_43).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 378953/5000000) (δ := 529/50000000) (ψ := -750661/1000000) 247 74
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t43 : ((291072971959/2000000000000 : ℚ) : ℝ) ≤ stT247o2 43 := by
  have hc : ((954347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((43 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291072971959/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((954347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c44 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4730237/2500000 : ℚ) : ℝ) ≤ Real.log ((44 : ℕ)) / 2 := by
    have h := (log_br_44).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((44 : ℕ)) / 2 ≤ ((37841897/20000000 : ℚ) : ℝ) := by
    have h := (log_br_44).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1963011/2500000) (δ := 853/100000000) (ψ := -750661/1000000) 247 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t44 : ((-30152647557/200000000000 : ℚ) : ℝ) ≤ stT247o2 44 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((44 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30152647557/200000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c45 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((466987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((594791/312500 : ℚ) : ℝ) ≤ Real.log ((45 : ℕ)) / 2 := by
    have h := (log_br_45).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((45 : ℕ)) / 2 ≤ ((304533/160000 : ℚ) : ℝ) := by
    have h := (log_br_45).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -913549/10000000) (δ := 221/20000000) (ψ := -750661/1000000) 247 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t45 : ((348052694991/2500000000000 : ℚ) : ℝ) ≤ stT247o2 45 := by
  have hc : ((233481/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((45 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348052694991/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((233481/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c46 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-21937/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((38286413/20000000 : ℚ) : ℝ) ≤ Real.log ((46 : ℕ)) / 2 := by
    have h := (log_br_46).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((46 : ℕ)) / 2 ≤ ((19143207/10000000 : ℚ) : ℝ) := by
    have h := (log_br_46).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2936219/5000000) (δ := 117/10000000) (ψ := -750661/1000000) 247 75
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t46 : ((-25877324257/250000000000 : ℚ) : ℝ) ≤ stT247o2 46 := by
  have hc : ((-351017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((46 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25877324257/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-351017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c47 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((57689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9625369/5000000 : ℚ) : ℝ) ≤ Real.log ((47 : ℕ)) / 2 := by
    have h := (log_br_47).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((47 : ℕ)) / 2 ≤ ((38501477/20000000 : ℚ) : ℝ) := by
    have h := (log_br_47).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -798871/2500000) (δ := 611/50000000) (ψ := -750661/1000000) 247 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t47 : ((84133415671/2000000000000 : ℚ) : ℝ) ≤ stT247o2 47 := by
  have hc : ((57679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((47 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84133415671/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((57679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c48 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((61583/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3871201/2000000 : ℚ) : ℝ) ≤ Real.log ((48 : ℕ)) / 2 := by
    have h := (log_br_48).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((48 : ℕ)) / 2 ≤ ((38712011/20000000 : ℚ) : ℝ) := by
    have h := (log_br_48).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 826189/2500000) (δ := 139/12500000) (ψ := -750661/1000000) 247 76
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t48 : ((1421909127/40000000000 : ℚ) : ℝ) ≤ stT247o2 48 := by
  have hc : ((123141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((48 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1421909127/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((123141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c49 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-74731/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((19459101/10000000 : ℚ) : ℝ) ≤ Real.log ((49 : ℕ)) / 2 := by
    have h := (log_br_49).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((49 : ℕ)) / 2 ≤ ((38918203/20000000 : ℚ) : ℝ) := by
    have h := (log_br_49).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6037003/10000000) (δ := 1177/100000000) (ψ := -750661/1000000) 247 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t49 : ((-1668214953/15625000000 : ℚ) : ℝ) ≤ stT247o2 49 := by
  have hc : ((-4671/6250 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((49 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1668214953/15625000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-4671/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c50 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((996783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3912023/2000000 : ℚ) : ℝ) ≤ Real.log ((50 : ℕ)) / 2 := by
    have h := (log_br_50).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((50 : ℕ)) / 2 ≤ ((39120231/20000000 : ℚ) : ℝ) := by
    have h := (log_br_50).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 200583/10000000) (δ := 1201/100000000) (ψ := -750661/1000000) 247 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t50 : ((1409592766129/10000000000000 : ℚ) : ℝ) ≤ stT247o2 50 := by
  have hc : ((996733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((50 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1409592766129/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((996733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c51 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-816349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2457391/1250000 : ℚ) : ℝ) ≤ Real.log ((51 : ℕ)) / 2 := by
    have h := (log_br_51).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((51 : ℕ)) / 2 ≤ ((39318257/20000000 : ℚ) : ℝ) := by
    have h := (log_br_51).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1578661/2500000) (δ := 871/100000000) (ψ := -750661/1000000) 247 77
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t51 : ((-1143188008119/10000000000000 : ℚ) : ℝ) ≤ stT247o2 51 := by
  have hc : ((-816399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((51 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1143188008119/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-816399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c52 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((210027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39512437/20000000 : ℚ) : ℝ) ≤ Real.log ((52 : ℕ)) / 2 := by
    have h := (log_br_52).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((52 : ℕ)) / 2 ≤ ((19756219/10000000 : ℚ) : ℝ) := by
    have h := (log_br_52).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -679597/2000000) (δ := 207/20000000) (ψ := -750661/1000000) 247 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t52 : ((1164742419/40000000000 : ℚ) : ℝ) ≤ stT247o2 52 := by
  have hc : ((209977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((52 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1164742419/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((209977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c53 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((545963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39702919/20000000 : ℚ) : ℝ) ≤ Real.log ((53 : ℕ)) / 2 := by
    have h := (log_br_53).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((53 : ℕ)) / 2 ≤ ((992573/500000 : ℚ) : ℝ) := by
    have h := (log_br_53).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 496629/2000000) (δ := 221/20000000) (ψ := -750661/1000000) 247 78
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t53 : ((149973765273/2000000000000 : ℚ) : ℝ) ≤ stT247o2 53 := by
  have hc : ((545913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((53 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149973765273/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((545913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c54 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-246801/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((498623/250000 : ℚ) : ℝ) ≤ Real.log ((54 : ℕ)) / 2 := by
    have h := (log_br_54).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((54 : ℕ)) / 2 ≤ ((39889841/20000000 : ℚ) : ℝ) := by
    have h := (log_br_54).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3726811/5000000) (δ := 69/10000000) (ψ := -750661/1000000) 247 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t54 : ((-167935360789/1250000000000 : ℚ) : ℝ) ≤ stT247o2 54 := by
  have hc : ((-493627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((54 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167935360789/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-493627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c55 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((754877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((40073331/20000000 : ℚ) : ℝ) ≤ Real.log ((55 : ℕ)) / 2 := by
    have h := (log_br_55).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((55 : ℕ)) / 2 ≤ ((10018333/5000000 : ℚ) : ℝ) := by
    have h := (log_br_55).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -71533/400000) (δ := 1043/100000000) (ψ := -750661/1000000) 247 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t55 : ((1017807971973/10000000000000 : ℚ) : ℝ) ≤ stT247o2 55 := by
  have hc : ((754827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((55 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1017807971973/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((754827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c56 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((15201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10063379/5000000 : ℚ) : ℝ) ≤ Real.log ((56 : ℕ)) / 2 := by
    have h := (log_br_56).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((56 : ℕ)) / 2 ≤ ((40253517/20000000 : ℚ) : ℝ) := by
    have h := (log_br_56).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 471861/1250000) (δ := 17/1562500) (ψ := -750661/1000000) 247 79
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t56 : ((20296483681/2500000000000 : ℚ) : ℝ) ≤ stT247o2 56 := by
  have hc : ((30377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((56 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20296483681/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((30377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c57 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-85029/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2526907/1250000 : ℚ) : ℝ) ≤ Real.log ((57 : ℕ)) / 2 := by
    have h := (log_br_57).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((57 : ℕ)) / 2 ≤ ((40430513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_57).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -646833/1000000) (δ := 839/100000000) (ψ := -750661/1000000) 247 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t57 : ((-56315169561/500000000000 : ℚ) : ℝ) ≤ stT247o2 57 := by
  have hc : ((-42517/50000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((57 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56315169561/500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-42517/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c58 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((180997/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4060443/2000000 : ℚ) : ℝ) ≤ Real.log ((58 : ℕ)) / 2 := by
    have h := (log_br_58).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((58 : ℕ)) / 2 ≤ ((40604431/20000000 : ℚ) : ℝ) := by
    have h := (log_br_58).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -109863/1000000) (δ := 1129/100000000) (ψ := -750661/1000000) 247 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t58 : ((29705939271/250000000000 : ℚ) : ℝ) ≤ stT247o2 58 := by
  have hc : ((180987/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((58 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29705939271/250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((180987/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c59 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-100743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20387687/10000000 : ℚ) : ℝ) ≤ Real.log ((59 : ℕ)) / 2 := by
    have h := (log_br_59).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((59 : ℕ)) / 2 ≤ ((326203/160000 : ℚ) : ℝ) := by
    have h := (log_br_59).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1044819/2500000) (δ := 729/100000000) (ψ := -750661/1000000) 247 80
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t59 : ((-13122139877/1000000000000 : ℚ) : ℝ) ≤ stT247o2 59 := by
  have hc : ((-100793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((59 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13122139877/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-100793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c60 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-822049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8188689/4000000 : ℚ) : ℝ) ≤ Real.log ((60 : ℕ)) / 2 := by
    have h := (log_br_60).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((60 : ℕ)) / 2 ≤ ((20471723/10000000 : ℚ) : ℝ) := by
    have h := (log_br_60).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6339489/10000000) (δ := 151/20000000) (ψ := -750661/1000000) 247 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t60 : ((-212265139701/2000000000000 : ℚ) : ℝ) ≤ stT247o2 60 := by
  have hc : ((-822099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((60 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212265139701/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-822099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c61 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((880241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((20554369/10000000 : ℚ) : ℝ) ≤ Real.log ((61 : ℕ)) / 2 := by
    have h := (log_br_61).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((61 : ℕ)) / 2 ≤ ((41108739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_61).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1236067/10000000) (δ := 39/5000000) (ψ := -750661/1000000) 247 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t61 : ((70435524393/625000000000 : ℚ) : ℝ) ≤ stT247o2 61 := by
  have hc : ((880191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((61 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70435524393/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((880191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c62 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((28509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41271343/20000000 : ℚ) : ℝ) ≤ Real.log ((62 : ℕ)) / 2 := by
    have h := (log_br_62).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((62 : ℕ)) / 2 ≤ ((2579459/1250000 : ℚ) : ℝ) := by
    have h := (log_br_62).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3784369/10000000) (δ := 209/20000000) (ψ := -750661/1000000) 247 81
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t62 : ((9043677121/1250000000000 : ℚ) : ℝ) ≤ stT247o2 62 := by
  have hc : ((7121/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((62 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9043677121/1250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((7121/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c63 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-939989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41431347/20000000 : ℚ) : ℝ) ≤ Real.log ((63 : ℕ)) / 2 := by
    have h := (log_br_63).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((63 : ℕ)) / 2 ≤ ((10357837/5000000 : ℚ) : ℝ) := by
    have h := (log_br_63).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6983489/10000000) (δ := 923/100000000) (ψ := -750661/1000000) 247 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t63 : ((-592169107699/5000000000000 : ℚ) : ℝ) ≤ stT247o2 63 := by
  have hc : ((-940039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((63 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592169107699/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-940039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c64 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((661129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4158883/2000000 : ℚ) : ℝ) ≤ Real.log ((64 : ℕ)) / 2 := by
    have h := (log_br_64).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((64 : ℕ)) / 2 ≤ ((41588831/20000000 : ℚ) : ℝ) := by
    have h := (log_br_64).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -66287/312500) (δ := 101/10000000) (ψ := -750661/1000000) 247 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t64 : ((661079/8000000 : ℚ) : ℝ) ≤ stT247o2 64 := by
  have hc : ((661079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((64 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((661079/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((661079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c65 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((120843/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((163062/78125 : ℚ) : ℝ) ≤ Real.log ((65 : ℕ)) / 2 := by
    have h := (log_br_65).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((65 : ℕ)) / 2 ≤ ((41743873/20000000 : ℚ) : ℝ) := by
    have h := (log_br_65).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1332867/5000000) (δ := 43/5000000) (ψ := -750661/1000000) 247 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t65 : ((299743496367/5000000000000 : ℚ) : ℝ) ≤ stT247o2 65 := by
  have hc : ((241661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((65 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299743496367/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((241661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c66 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-30689/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((41896547/20000000 : ℚ) : ℝ) ≤ Real.log ((66 : ℕ)) / 2 := by
    have h := (log_br_66).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((66 : ℕ)) / 2 ≤ ((10474137/5000000 : ℚ) : ℝ) := by
    have h := (log_br_66).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3689783/5000000) (δ := 723/100000000) (ψ := -750661/1000000) 247 82
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t66 : ((-120887915967/1000000000000 : ℚ) : ℝ) ≤ stT247o2 66 := by
  have hc : ((-491049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((66 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120887915967/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-491049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c67 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((19293/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21023463/10000000 : ℚ) : ℝ) ≤ Real.log ((67 : ℕ)) / 2 := by
    have h := (log_br_67).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((67 : ℕ)) / 2 ≤ ((42046927/20000000 : ℚ) : ℝ) := by
    have h := (log_br_67).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3685453/10000000) (δ := 1017/100000000) (ψ := -750661/1000000) 247 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t67 : ((11778962701/1000000000000 : ℚ) : ℝ) ≤ stT247o2 67 := by
  have hc : ((19283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((67 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11778962701/1000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((19283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c68 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((937479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42195077/20000000 : ℚ) : ℝ) ≤ Real.log ((68 : ℕ)) / 2 := by
    have h := (log_br_68).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((68 : ℕ)) / 2 ≤ ((21097539/10000000 : ℚ) : ℝ) := by
    have h := (log_br_68).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 177741/2000000) (δ := 591/50000000) (ψ := -750661/1000000) 247 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t68 : ((568399762431/5000000000000 : ℚ) : ℝ) ≤ stT247o2 68 := by
  have hc : ((937429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((68 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568399762431/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((937429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c69 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-138599/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((8468213/4000000 : ℚ) : ℝ) ≤ Real.log ((69 : ℕ)) / 2 := by
    have h := (log_br_69).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((69 : ℕ)) / 2 ≤ ((21170533/10000000 : ℚ) : ℝ) := by
    have h := (log_br_69).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1349021/2500000) (δ := 601/50000000) (ψ := -750661/1000000) 247 83
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t69 : ((-333737403557/5000000000000 : ℚ) : ℝ) ≤ stT247o2 69 := by
  have hc : ((-277223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((69 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333737403557/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-277223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c70 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-140221/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5310619/2500000 : ℚ) : ℝ) ≤ Real.log ((70 : ℕ)) / 2 := by
    have h := (log_br_70).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((70 : ℕ)) / 2 ≤ ((42484953/20000000 : ℚ) : ℝ) := by
    have h := (log_br_70).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5869357/10000000) (δ := 189/25000000) (ψ := -750661/1000000) 247 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t70 : ((-167608157899/2000000000000 : ℚ) : ℝ) ≤ stT247o2 70 := by
  have hc : ((-140231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((70 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167608157899/2000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-140231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c71 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((827621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21313399/10000000 : ℚ) : ℝ) ≤ Real.log ((71 : ℕ)) / 2 := by
    have h := (log_br_71).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((71 : ℕ)) / 2 ≤ ((42626799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_71).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -29797/200000) (δ := 119/12500000) (ψ := -750661/1000000) 247 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t71 : ((982145538951/10000000000000 : ℚ) : ℝ) ≤ stT247o2 71 := by
  have hc : ((827571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((71 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((982145538951/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((827571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c72 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((425429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((42766661/20000000 : ℚ) : ℝ) ≤ Real.log ((72 : ℕ)) / 2 := by
    have h := (log_br_72).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((72 : ℕ)) / 2 ≤ ((21383331/10000000 : ℚ) : ℝ) := by
    have h := (log_br_72).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1414201/5000000) (δ := 1011/100000000) (ψ := -750661/1000000) 247 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t72 : ((501313830669/10000000000000 : ℚ) : ℝ) ≤ stT247o2 72 := by
  have hc : ((425379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((72 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501313830669/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((425379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c73 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-476659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21452297/10000000 : ℚ) : ℝ) ≤ Real.log ((73 : ℕ)) / 2 := by
    have h := (log_br_73).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((73 : ℕ)) / 2 ≤ ((8580919/4000000 : ℚ) : ℝ) := by
    have h := (log_br_73).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 708709/1000000) (δ := 373/50000000) (ψ := -750661/1000000) 247 84
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t73 : ((-34869792113/312500000000 : ℚ) : ℝ) ≤ stT247o2 73 := by
  have hc : ((-119171/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((73 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34869792113/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-119171/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c74 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-97989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((860813/400000 : ℚ) : ℝ) ≤ Real.log ((74 : ℕ)) / 2 := by
    have h := (log_br_74).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((74 : ℕ)) / 2 ≤ ((43040651/20000000 : ℚ) : ℝ) := by
    have h := (log_br_74).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -138129/312500) (δ := 1143/100000000) (ψ := -750661/1000000) 247 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t74 : ((-56969510339/2500000000000 : ℚ) : ℝ) ≤ stT247o2 74 := by
  have hc : ((-49007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((74 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56969510339/2500000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-49007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c75 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((496961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43174881/20000000 : ℚ) : ℝ) ≤ Real.log ((75 : ℕ)) / 2 := by
    have h := (log_br_75).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((75 : ℕ)) / 2 ≤ ((21587441/10000000 : ℚ) : ℝ) := by
    have h := (log_br_75).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -275771/10000000) (δ := 11/1000000) (ψ := -750661/1000000) 247 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t75 : ((717264999/6250000000 : ℚ) : ℝ) ≤ stT247o2 75 := by
  have hc : ((62117/62500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((75 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((717264999/6250000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((62117/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c76 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((5663/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43307333/20000000 : ℚ) : ℝ) ≤ Real.log ((76 : ℕ)) / 2 := by
    have h := (log_br_76).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((76 : ℕ)) / 2 ≤ ((21653667/10000000 : ℚ) : ℝ) := by
    have h := (log_br_76).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3813693/10000000) (δ := 19/2500000) (ψ := -750661/1000000) 247 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t76 : ((12977466953/2500000000000 : ℚ) : ℝ) ≤ stT247o2 76 := by
  have hc : ((22627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((76 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12977466953/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((22627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c77 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21719027/10000000 : ℚ) : ℝ) ≤ Real.log ((77 : ℕ)) / 2 := by
    have h := (log_br_77).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((77 : ℕ)) / 2 ≤ ((8687611/4000000 : ℚ) : ℝ) := by
    have h := (log_br_77).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3924849/5000000) (δ := 199/20000000) (ψ := -750661/1000000) 247 85
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t77 : ((-569830920347/5000000000000 : ℚ) : ℝ) ≤ stT247o2 77 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((77 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-569830920347/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c78 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((21059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2722943/1250000 : ℚ) : ℝ) ≤ Real.log ((78 : ℕ)) / 2 := by
    have h := (log_br_78).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((78 : ℕ)) / 2 ≤ ((43567089/20000000 : ℚ) : ℝ) := by
    have h := (log_br_78).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3874339/10000000) (δ := 187/20000000) (ψ := -750661/1000000) 247 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t78 : ((23788007493/10000000000000 : ℚ) : ℝ) ≤ stT247o2 78 := by
  have hc : ((21009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((78 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23788007493/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((21009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c79 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((999723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21847239/10000000 : ℚ) : ℝ) ≤ Real.log ((79 : ℕ)) / 2 := by
    have h := (log_br_79).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((79 : ℕ)) / 2 ≤ ((43694479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_79).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 11767/2000000) (δ := 1/160000) (ψ := -750661/1000000) 247 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t79 : ((1124719096551/10000000000000 : ℚ) : ℝ) ≤ stT247o2 79 := by
  have hc : ((999673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((79 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1124719096551/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((999673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c80 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-6217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((21910133/10000000 : ℚ) : ℝ) ≤ Real.log ((80 : ℕ)) / 2 := by
    have h := (log_br_80).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((80 : ℕ)) / 2 ≤ ((43820267/20000000 : ℚ) : ℝ) := by
    have h := (log_br_80).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1971267/5000000) (δ := 169/20000000) (ψ := -750661/1000000) 247 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t80 : ((-3503359539/5000000000000 : ℚ) : ℝ) ≤ stT247o2 80 := by
  have hc : ((-6267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((80 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3503359539/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-6267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c81 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-499769/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((43944491/20000000 : ℚ) : ℝ) ≤ Real.log ((81 : ℕ)) / 2 := by
    have h := (log_br_81).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((81 : ℕ)) / 2 ≤ ((10986123/5000000 : ℚ) : ℝ) := by
    have h := (log_br_81).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 7777987/10000000) (δ := 319/50000000) (ψ := -750661/1000000) 247 86
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t81 : ((-34707944433/312500000000 : ℚ) : ℝ) ≤ stT247o2 81 := by
  have hc : ((-249897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((81 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34707944433/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-249897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c82 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-21433/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5508399/2500000 : ℚ) : ℝ) ≤ Real.log ((82 : ℕ)) / 2 := by
    have h := (log_br_82).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((82 : ℕ)) / 2 ≤ ((44067193/20000000 : ℚ) : ℝ) := by
    have h := (log_br_82).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -828317/2000000) (δ := 171/25000000) (ψ := -750661/1000000) 247 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t82 : ((-11841304389/1250000000000 : ℚ) : ℝ) ≤ stT247o2 82 := by
  have hc : ((-42891/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((82 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11841304389/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-42891/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c83 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((246821/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22094203/10000000 : ℚ) : ℝ) ≤ Real.log ((83 : ℕ)) / 2 := by
    have h := (log_br_83).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((83 : ℕ)) / 2 ≤ ((44188407/20000000 : ℚ) : ℝ) := by
    have h := (log_br_83).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -79823/2000000) (δ := 587/50000000) (ψ := -750661/1000000) 247 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t83 : ((270907375557/2500000000000 : ℚ) : ℝ) ≤ stT247o2 83 := by
  have hc : ((493617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((83 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270907375557/2500000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((493617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c84 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((248743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44308167/20000000 : ℚ) : ℝ) ≤ Real.log ((84 : ℕ)) / 2 := by
    have h := (log_br_84).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((84 : ℕ)) / 2 ≤ ((44308169/20000000 : ℚ) : ℝ) := by
    have h := (log_br_84).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1649267/5000000) (δ := 321/25000000) (ψ := -750661/1000000) 247 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t84 : ((271346196677/10000000000000 : ℚ) : ℝ) ≤ stT247o2 84 := by
  have hc : ((248693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((84 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271346196677/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((248693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c85 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-935677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2776657/1250000 : ℚ) : ℝ) ≤ Real.log ((85 : ℕ)) / 2 := by
    have h := (log_br_85).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((85 : ℕ)) / 2 ≤ ((44426513/20000000 : ℚ) : ℝ) := by
    have h := (log_br_85).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6952423/10000000) (δ := 337/50000000) (ψ := -750661/1000000) 247 87
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t85 : ((-1014939097731/10000000000000 : ℚ) : ℝ) ≤ stT247o2 85 := by
  have hc : ((-935727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((85 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1014939097731/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-935727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c86 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-23397/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2783967/1250000 : ℚ) : ℝ) ≤ Real.log ((86 : ℕ)) / 2 := by
    have h := (log_br_86).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((86 : ℕ)) / 2 ≤ ((44543473/20000000 : ℚ) : ℝ) := by
    have h := (log_br_86).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1286097/2500000) (δ := 233/20000000) (ψ := -750661/1000000) 247 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t86 : ((-6308084009/125000000000 : ℚ) : ℝ) ≤ stT247o2 86 := by
  have hc : ((-46799/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((86 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6308084009/125000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-46799/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c87 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((808031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44659081/20000000 : ℚ) : ℝ) ≤ Real.log ((87 : ℕ)) / 2 := by
    have h := (log_br_87).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((87 : ℕ)) / 2 ≤ ((22329541/10000000 : ℚ) : ℝ) := by
    have h := (log_br_87).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -196873/1250000) (δ := 257/25000000) (ψ := -750661/1000000) 247 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t87 : ((54140382867/625000000000 : ℚ) : ℝ) ≤ stT247o2 87 := by
  have hc : ((807981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((87 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54140382867/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((807981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c88 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((709893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5596671/2500000 : ℚ) : ℝ) ≤ Real.log ((88 : ℕ)) / 2 := by
    have h := (log_br_88).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((88 : ℕ)) / 2 ≤ ((44773369/20000000 : ℚ) : ℝ) := by
    have h := (log_br_88).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 976813/5000000) (δ := 1073/100000000) (ψ := -750661/1000000) 247 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t88 : ((756694767529/10000000000000 : ℚ) : ℝ) ≤ stT247o2 88 := by
  have hc : ((709843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((88 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((756694767529/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((709843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c89 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-569707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((44886363/20000000 : ℚ) : ℝ) ≤ Real.log ((89 : ℕ)) / 2 := by
    have h := (log_br_89).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((89 : ℕ)) / 2 ≤ ((11221591/5000000 : ℚ) : ℝ) := by
    have h := (log_br_89).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1360591/2500000) (δ := 43/5000000) (ψ := -750661/1000000) 247 88
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t89 : ((-301970640243/5000000000000 : ℚ) : ℝ) ≤ stT247o2 89 := by
  have hc : ((-569757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((89 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-301970640243/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-569757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c90 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-915013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2812381/1250000 : ℚ) : ℝ) ≤ Real.log ((90 : ℕ)) / 2 := by
    have h := (log_br_90).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((90 : ℕ)) / 2 ≤ ((44998097/20000000 : ℚ) : ℝ) := by
    have h := (log_br_90).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6815843/10000000) (δ := 171/20000000) (ψ := -750661/1000000) 247 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t90 : ((-964561502859/10000000000000 : ℚ) : ℝ) ≤ stT247o2 90 := by
  have hc : ((-915063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((90 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-964561502859/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-915063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c91 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((207593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22554297/10000000 : ℚ) : ℝ) ≤ Real.log ((91 : ℕ)) / 2 := by
    have h := (log_br_91).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((91 : ℕ)) / 2 ≤ ((11277149/5000000 : ℚ) : ℝ) := by
    have h := (log_br_91).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1702103/5000000) (δ := 261/20000000) (ψ := -750661/1000000) 247 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t91 : ((54391001553/2500000000000 : ℚ) : ℝ) ≤ stT247o2 91 := by
  have hc : ((207543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((91 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54391001553/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((207543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c92 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((999929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9043577/4000000 : ℚ) : ℝ) ≤ Real.log ((92 : ℕ)) / 2 := by
    have h := (log_br_92).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((92 : ℕ)) / 2 ≤ ((22608943/10000000 : ℚ) : ℝ) := by
    have h := (log_br_92).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -933/312500) (δ := 23/2500000) (ψ := -750661/1000000) 247 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t92 : ((260611462197/2500000000000 : ℚ) : ℝ) ≤ stT247o2 92 := by
  have hc : ((999879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((92 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260611462197/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((999879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c93 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((61267/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22662997/10000000 : ℚ) : ℝ) ≤ Real.log ((93 : ℕ)) / 2 := by
    have h := (log_br_93).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((93 : ℕ)) / 2 ≤ ((9065199/4000000 : ℚ) : ℝ) := by
    have h := (log_br_93).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 661603/2000000) (δ := 229/20000000) (ψ := -750661/1000000) 247 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t93 : ((127035830059/5000000000000 : ℚ) : ℝ) ≤ stT247o2 93 := by
  have hc : ((122509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((93 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((127035830059/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((122509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c94 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-878769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45432947/20000000 : ℚ) : ℝ) ≤ Real.log ((94 : ℕ)) / 2 := by
    have h := (log_br_94).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((94 : ℕ)) / 2 ≤ ((11358237/5000000 : ℚ) : ℝ) := by
    have h := (log_br_94).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1322037/2000000) (δ := 99/10000000) (ψ := -750661/1000000) 247 89
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t94 : ((-453216625309/5000000000000 : ℚ) : ℝ) ≤ stT247o2 94 := by
  have hc : ((-878819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((94 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453216625309/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-878819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c95 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-689953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2846173/1250000 : ℚ) : ℝ) ≤ Real.log ((95 : ℕ)) / 2 := by
    have h := (log_br_95).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((95 : ℕ)) / 2 ≤ ((45538769/20000000 : ℚ) : ℝ) := by
    have h := (log_br_95).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -728819/1250000) (δ := 553/50000000) (ψ := -750661/1000000) 247 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t95 : ((-707928587937/10000000000000 : ℚ) : ℝ) ≤ stT247o2 95 := by
  have hc : ((-690003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((95 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-707928587937/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-690003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c96 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((507069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45643481/20000000 : ℚ) : ℝ) ≤ Real.log ((96 : ℕ)) / 2 := by
    have h := (log_br_96).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((96 : ℕ)) / 2 ≤ ((22821741/10000000 : ℚ) : ℝ) := by
    have h := (log_br_96).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1298769/5000000) (δ := 1111/100000000) (ψ := -750661/1000000) 247 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t96 : ((25873686589/500000000000 : ℚ) : ℝ) ≤ stT247o2 96 := by
  have hc : ((507019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((96 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25873686589/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((507019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c97 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((19423/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((45747109/20000000 : ℚ) : ℝ) ≤ Real.log ((97 : ℕ)) / 2 := by
    have h := (log_br_97).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((97 : ℕ)) / 2 ≤ ((4574711/2000000 : ℚ) : ℝ) := by
    have h := (log_br_97).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 150493/2500000) (δ := 931/100000000) (ψ := -750661/1000000) 247 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t97 : ((4930012503/50000000000 : ℚ) : ℝ) ≤ stT247o2 97 := by
  have hc : ((9711/10000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((97 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4930012503/50000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((9711/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c98 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((63287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22924837/10000000 : ℚ) : ℝ) ≤ Real.log ((98 : ℕ)) / 2 := by
    have h := (log_br_98).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((98 : ℕ)) / 2 ≤ ((1833987/800000 : ℚ) : ℝ) := by
    have h := (log_br_98).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3768667/10000000) (δ := 239/25000000) (ψ := -750661/1000000) 247 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t98 : ((7984872753/1250000000000 : ℚ) : ℝ) ≤ stT247o2 98 := by
  have hc : ((63237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((98 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7984872753/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((63237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c99 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-18571/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((22975599/10000000 : ℚ) : ℝ) ≤ Real.log ((99 : ℕ)) / 2 := by
    have h := (log_br_99).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((99 : ℕ)) / 2 ≤ ((45951199/20000000 : ℚ) : ℝ) := by
    have h := (log_br_99).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1725803/2500000) (δ := 311/50000000) (ψ := -750661/1000000) 247 90
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t99 : ((-2333195717/25000000000 : ℚ) : ℝ) ≤ stT247o2 99 := by
  have hc : ((-4643/5000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((99 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2333195717/25000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-4643/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c100 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-651749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46051701/20000000 : ℚ) : ℝ) ≤ Real.log ((100 : ℕ)) / 2 := by
    have h := (log_br_100).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((100 : ℕ)) / 2 ≤ ((23025851/10000000 : ℚ) : ℝ) := by
    have h := (log_br_100).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -570171/1000000) (δ := 531/50000000) (ψ := -750661/1000000) 247 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t100 : ((-651799/10000000 : ℚ) : ℝ) ≤ stT247o2 100 := by
  have hc : ((-651799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((100 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-651799/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-651799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c101 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((495993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9230241/4000000 : ℚ) : ℝ) ≤ Real.log ((101 : ℕ)) / 2 := by
    have h := (log_br_101).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((101 : ℕ)) / 2 ≤ ((23075603/10000000 : ℚ) : ℝ) := by
    have h := (log_br_101).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1314773/5000000) (δ := 33/3125000) (ψ := -750661/1000000) 247 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t101 : ((493481634891/10000000000000 : ℚ) : ℝ) ≤ stT247o2 101 := by
  have hc : ((495943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((101 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493481634891/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((495943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c102 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((246607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((180663/78125 : ℚ) : ℝ) ≤ Real.log ((102 : ℕ)) / 2 := by
    have h := (log_br_102).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((102 : ℕ)) / 2 ≤ ((46249729/20000000 : ℚ) : ℝ) := by
    have h := (log_br_102).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 412351/10000000) (δ := 1081/100000000) (ψ := -750661/1000000) 247 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t102 : ((488329608783/5000000000000 : ℚ) : ℝ) ≤ stT247o2 102 := by
  have hc : ((493189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((102 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((488329608783/5000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((493189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c103 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((99809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46347289/20000000 : ℚ) : ℝ) ≤ Real.log ((103 : ℕ)) / 2 := by
    have h := (log_br_103).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((103 : ℕ)) / 2 ≤ ((4634729/2000000 : ℚ) : ℝ) := by
    have h := (log_br_103).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 342457/1000000) (δ := 541/50000000) (ψ := -750661/1000000) 247 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t103 : ((12290008617/625000000000 : ℚ) : ℝ) ≤ stT247o2 103 := by
  have hc : ((12473/62500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((103 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12290008617/625000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((12473/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c104 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-418637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11610977/5000000 : ℚ) : ℝ) ≤ Real.log ((104 : ℕ)) / 2 := by
    have h := (log_br_104).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((104 : ℕ)) / 2 ≤ ((46443909/20000000 : ℚ) : ℝ) := by
    have h := (log_br_104).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1281537/2000000) (δ := 1217/100000000) (ψ := -750661/1000000) 247 91
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t104 : ((-205266001311/2500000000000 : ℚ) : ℝ) ≤ stT247o2 104 := by
  have hc : ((-209331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((104 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205266001311/2500000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-209331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c105 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-823463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((46539603/20000000 : ℚ) : ℝ) ≤ Real.log ((105 : ℕ)) / 2 := by
    have h := (log_br_105).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((105 : ℕ)) / 2 ≤ ((11634901/5000000 : ℚ) : ℝ) := by
    have h := (log_br_105).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6345711/10000000) (δ := 131/20000000) (ψ := -750661/1000000) 247 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t105 : ((-803667160213/10000000000000 : ℚ) : ℝ) ≤ stT247o2 105 := by
  have hc : ((-823513/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((105 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-803667160213/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-823513/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c106 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((201743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4663439/2000000 : ℚ) : ℝ) ≤ Real.log ((106 : ℕ)) / 2 := by
    have h := (log_br_106).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((106 : ℕ)) / 2 ≤ ((46634391/20000000 : ℚ) : ℝ) := by
    have h := (log_br_106).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -854787/2500000) (δ := 579/50000000) (ψ := -750661/1000000) 247 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t106 : ((39180277101/2000000000000 : ℚ) : ℝ) ≤ stT247o2 106 := by
  have hc : ((201693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((106 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39180277101/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((201693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c107 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((24461/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1460259/625000 : ℚ) : ℝ) ≤ Real.log ((107 : ℕ)) / 2 := by
    have h := (log_br_107).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((107 : ℕ)) / 2 ≤ ((46728289/20000000 : ℚ) : ℝ) := by
    have h := (log_br_107).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -260033/5000000) (δ := 83/10000000) (ψ := -750661/1000000) 247 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t107 : ((5911530219/62500000000 : ℚ) : ℝ) ≤ stT247o2 107 := by
  have hc : ((97839/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((107 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5911530219/62500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((97839/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c108 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((294563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((731583/312500 : ℚ) : ℝ) ≤ Real.log ((108 : ℕ)) / 2 := by
    have h := (log_br_108).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((108 : ℕ)) / 2 ≤ ((46821313/20000000 : ℚ) : ℝ) := by
    have h := (log_br_108).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 147003/625000) (δ := 91/10000000) (ψ := -750661/1000000) 247 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t108 : ((566838381/10000000000 : ℚ) : ℝ) ≤ stT247o2 108 := by
  have hc : ((147269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((108 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566838381/10000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((147269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c109 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-19467/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23456739/10000000 : ℚ) : ℝ) ≤ Real.log ((109 : ℕ)) / 2 := by
    have h := (log_br_109).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((109 : ℕ)) / 2 ≤ ((46913479/20000000 : ℚ) : ℝ) := by
    have h := (log_br_109).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 519769/1000000) (δ := 499/50000000) (ψ := -750661/1000000) 247 92
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t109 : ((-18647933863/400000000000 : ℚ) : ℝ) ≤ stT247o2 109 := by
  have hc : ((-19469/40000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((109 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18647933863/400000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-19469/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c110 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-498933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47004803/20000000 : ℚ) : ℝ) ≤ Real.log ((110 : ℕ)) / 2 := by
    have h := (log_br_110).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((110 : ℕ)) / 2 ≤ ((11751201/5000000 : ℚ) : ℝ) := by
    have h := (log_br_110).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7690619/10000000) (δ := 793/100000000) (ψ := -750661/1000000) 247 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t110 : ((-237868995777/2500000000000 : ℚ) : ℝ) ≤ stT247o2 110 := by
  have hc : ((-249479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((110 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237868995777/2500000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-249479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c111 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-378149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23547651/10000000 : ℚ) : ℝ) ≤ Real.log ((111 : ℕ)) / 2 := by
    have h := (log_br_111).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((111 : ℕ)) / 2 ≤ ((47095303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_111).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2448241/5000000) (δ := 123/10000000) (ψ := -750661/1000000) 247 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t111 : ((-179485303221/5000000000000 : ℚ) : ℝ) ≤ stT247o2 111 := by
  have hc : ((-378199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((111 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179485303221/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-378199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c112 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((32963/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11796247/5000000 : ℚ) : ℝ) ≤ Real.log ((112 : ℕ)) / 2 := by
    have h := (log_br_112).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((112 : ℕ)) / 2 ≤ ((47184989/20000000 : ℚ) : ℝ) := by
    have h := (log_br_112).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -425481/2000000) (δ := 439/50000000) (ψ := -750661/1000000) 247 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t112 : ((62289478031/1000000000000 : ℚ) : ℝ) ≤ stT247o2 112 := by
  have hc : ((65921/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((112 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62289478031/1000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((65921/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c113 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((484847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23636939/10000000 : ℚ) : ℝ) ≤ Real.log ((113 : ℕ)) / 2 := by
    have h := (log_br_113).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((113 : ℕ)) / 2 ≤ ((47273879/20000000 : ℚ) : ℝ) := by
    have h := (log_br_113).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 617057/10000000) (δ := 103/10000000) (ψ := -750661/1000000) 247 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t113 : ((2850510949/31250000000 : ℚ) : ℝ) ≤ stT247o2 113 := by
  have hc : ((242411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((113 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2850510949/31250000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((242411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c114 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((2921/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((740031/312500 : ℚ) : ℝ) ≤ Real.log ((114 : ℕ)) / 2 := by
    have h := (log_br_114).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((114 : ℕ)) / 2 ≤ ((9472397/4000000 : ℚ) : ℝ) := by
    have h := (log_br_114).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3337339/10000000) (δ := 33/5000000) (ψ := -750661/1000000) 247 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t114 : ((4376287071/200000000000 : ℚ) : ℝ) ≤ stT247o2 114 := by
  have hc : ((23363/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((114 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4376287071/200000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((23363/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c115 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-29859/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47449321/20000000 : ℚ) : ℝ) ≤ Real.log ((115 : ℕ)) / 2 := by
    have h := (log_br_115).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((115 : ℕ)) / 2 ≤ ((23724661/10000000 : ℚ) : ℝ) := by
    have h := (log_br_115).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6033863/10000000) (δ := 179/20000000) (ψ := -750661/1000000) 247 93
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t115 : ((-5569106361/80000000000 : ℚ) : ℝ) ≤ stT247o2 115 := by
  have hc : ((-29861/40000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((115 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5569106361/80000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-29861/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c116 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-471173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47535901/20000000 : ℚ) : ℝ) ≤ Real.log ((116 : ℕ)) / 2 := by
    have h := (log_br_116).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((116 : ℕ)) / 2 ≤ ((23767951/10000000 : ℚ) : ℝ) := by
    have h := (log_br_116).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1750231/2500000) (δ := 547/50000000) (ψ := -750661/1000000) 247 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t116 : ((-218748252723/2500000000000 : ℚ) : ℝ) ≤ stT247o2 116 := by
  have hc : ((-235599/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((116 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218748252723/2500000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-235599/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c117 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-168671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47621739/20000000 : ℚ) : ℝ) ≤ Real.log ((117 : ℕ)) / 2 := by
    have h := (log_br_117).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((117 : ℕ)) / 2 ≤ ((2381087/1000000 : ℚ) : ℝ) := by
    have h := (log_br_117).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4350693/10000000) (δ := 417/50000000) (ψ := -750661/1000000) 247 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t117 : ((-155982733221/10000000000000 : ℚ) : ℝ) ≤ stT247o2 117 := by
  have hc : ((-168721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((117 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155982733221/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-168721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c118 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((771751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23853423/10000000 : ℚ) : ℝ) ≤ Real.log ((118 : ℕ)) / 2 := by
    have h := (log_br_118).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((118 : ℕ)) / 2 ≤ ((47706847/20000000 : ℚ) : ℝ) := by
    have h := (log_br_118).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1723017/10000000) (δ := 939/100000000) (ψ := -750661/1000000) 247 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t118 : ((355203938187/5000000000000 : ℚ) : ℝ) ≤ stT247o2 118 := by
  have hc : ((771701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((118 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((355203938187/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((771701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c119 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((469171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((23895617/10000000 : ℚ) : ℝ) ≤ Real.log ((119 : ℕ)) / 2 := by
    have h := (log_br_119).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((119 : ℕ)) / 2 ≤ ((9558247/4000000 : ℚ) : ℝ) := by
    have h := (log_br_119).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 882483/10000000) (δ := 1119/100000000) (ψ := -750661/1000000) 247 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t119 : ((107516299977/1250000000000 : ℚ) : ℝ) ≤ stT247o2 119 := by
  have hc : ((234573/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((119 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107516299977/1250000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((234573/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c120 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((91641/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((47874917/20000000 : ℚ) : ℝ) ≤ Real.log ((120 : ℕ)) / 2 := by
    have h := (log_br_120).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((120 : ℕ)) / 2 ≤ ((23937459/10000000 : ℚ) : ℝ) := by
    have h := (log_br_120).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 173309/500000) (δ := 93/12500000) (ψ := -750661/1000000) 247 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t120 : ((261354681/15625000000 : ℚ) : ℝ) ≤ stT247o2 120 := by
  have hc : ((2863/15625 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((120 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261354681/15625000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((2863/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c121 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-745029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9591581/4000000 : ℚ) : ℝ) ≤ Real.log ((121 : ℕ)) / 2 := by
    have h := (log_br_121).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((121 : ℕ)) / 2 ≤ ((23978953/10000000 : ℚ) : ℝ) := by
    have h := (log_br_121).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1507109/2500000) (δ := 171/25000000) (ψ := -750661/1000000) 247 94
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t121 : ((-677344613189/10000000000000 : ℚ) : ℝ) ≤ stT247o2 121 := by
  have hc : ((-745079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((121 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-677344613189/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-745079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c122 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-95931/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4804021/2000000 : ℚ) : ℝ) ≤ Real.log ((122 : ℕ)) / 2 := by
    have h := (log_br_122).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((122 : ℕ)) / 2 ≤ ((48040211/20000000 : ℚ) : ℝ) := by
    have h := (log_br_122).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7138361/10000000) (δ := 177/25000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t122 : ((-678565821/7812500000 : ℚ) : ℝ) ≤ stT247o2 122 := by
  have hc : ((-2998/3125 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((122 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-678565821/7812500000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-2998/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c123 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-136437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48121843/20000000 : ℚ) : ℝ) ≤ Real.log ((123 : ℕ)) / 2 := by
    have h := (log_br_123).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((123 : ℕ)) / 2 ≤ ((12030461/5000000 : ℚ) : ℝ) := by
    have h := (log_br_123).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4617939/10000000) (δ := 131/20000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t123 : ((-6152184577/250000000000 : ℚ) : ℝ) ≤ stT247o2 123 := by
  have hc : ((-68231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((123 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6152184577/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-68231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c124 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((662107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((9640563/4000000 : ℚ) : ℝ) ≤ Real.log ((124 : ℕ)) / 2 := by
    have h := (log_br_124).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((124 : ℕ)) / 2 ≤ ((753169/312500 : ℚ) : ℝ) := by
    have h := (log_br_124).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -84717/400000) (δ := 159/20000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t124 : ((297272199741/5000000000000 : ℚ) : ℝ) ≤ stT247o2 124 := by
  have hc : ((662057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((124 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((297272199741/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((662057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c125 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((494767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48283137/20000000 : ℚ) : ℝ) ≤ Real.log ((125 : ℕ)) / 2 := by
    have h := (log_br_125).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((125 : ℕ)) / 2 ≤ ((24141569/10000000 : ℚ) : ℝ) := by
    have h := (log_br_125).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 45251/1250000) (δ := 793/100000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t125 : ((221255301417/2500000000000 : ℚ) : ℝ) ≤ stT247o2 125 := by
  have hc : ((247371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((125 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221255301417/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((247371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c126 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((2673/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48362819/20000000 : ℚ) : ℝ) ≤ Real.log ((126 : ℕ)) / 2 := by
    have h := (log_br_126).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((126 : ℕ)) / 2 ≤ ((2418141/1000000 : ℚ) : ℝ) := by
    have h := (log_br_126).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 141109/500000) (δ := 1183/100000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t126 : ((3809627381/100000000000 : ℚ) : ℝ) ≤ stT247o2 126 := by
  have hc : ((42763/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((126 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3809627381/100000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((42763/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c127 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-101859/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4844187/2000000 : ℚ) : ℝ) ≤ Real.log ((127 : ℕ)) / 2 := by
    have h := (log_br_127).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((127 : ℕ)) / 2 ≤ ((48441871/20000000 : ℚ) : ℝ) := by
    have h := (log_br_127).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 657863/1250000) (δ := 103/10000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t127 : ((-90394170233/2000000000000 : ℚ) : ℝ) ≤ stT247o2 127 := by
  have hc : ((-101869/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((127 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90394170233/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-101869/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c128 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-997703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24260151/10000000 : ℚ) : ℝ) ≤ Real.log ((128 : ℕ)) / 2 := by
    have h := (log_br_128).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((128 : ℕ)) / 2 ≤ ((48520303/20000000 : ℚ) : ℝ) := by
    have h := (log_br_128).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3842243/5000000) (δ := 79/10000000) (ψ := -750661/1000000) 247 95
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t128 : ((-220474478163/2500000000000 : ℚ) : ℝ) ≤ stT247o2 128 := by
  have hc : ((-997753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((128 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220474478163/2500000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-997753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c129 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-626847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12149531/5000000 : ℚ) : ℝ) ≤ Real.log ((129 : ℕ)) / 2 := by
    have h := (log_br_129).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((129 : ℕ)) / 2 ≤ ((77757/32000 : ℚ) : ℝ) := by
    have h := (log_br_129).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2810371/5000000) (δ := 151/12500000) (ψ := -750661/1000000) 247 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t129 : ((-551952090547/10000000000000 : ℚ) : ℝ) ≤ stT247o2 129 := by
  have hc : ((-626897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((129 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-551952090547/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-626897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c130 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((10907/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3042209/1250000 : ℚ) : ℝ) ≤ Real.log ((130 : ℕ)) / 2 := by
    have h := (log_br_130).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((130 : ℕ)) / 2 ≤ ((9735069/4000000 : ℚ) : ℝ) := by
    have h := (log_br_130).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -40457/125000) (δ := 157/25000000) (ψ := -750661/1000000) 247 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t130 : ((956431749/40000000000 : ℚ) : ℝ) ≤ stT247o2 130 := by
  have hc : ((2181/8000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((130 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956431749/40000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((2181/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c131 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((14687/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48751973/20000000 : ℚ) : ℝ) ≤ Real.log ((131 : ℕ)) / 2 := by
    have h := (log_br_131).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((131 : ℕ)) / 2 ≤ ((24375987/10000000 : ℚ) : ℝ) := by
    have h := (log_br_131).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -108831/1250000) (δ := 963/100000000) (ψ := -750661/1000000) 247 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t131 : ((51325632267/625000000000 : ℚ) : ℝ) ≤ stT247o2 131 := by
  have hc : ((469959/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((131 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51325632267/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((469959/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c132 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((166087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48828019/20000000 : ℚ) : ℝ) ≤ Real.log ((132 : ℕ)) / 2 := by
    have h := (log_br_132).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((132 : ℕ)) / 2 ≤ ((2441401/1000000 : ℚ) : ℝ) := by
    have h := (log_br_132).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 184659/1250000) (δ := 973/100000000) (ψ := -750661/1000000) 247 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t132 : ((36137856969/500000000000 : ℚ) : ℝ) ≤ stT247o2 132 := by
  have hc : ((166077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((132 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36137856969/500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((166077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c133 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((47789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48903491/20000000 : ℚ) : ℝ) ≤ Real.log ((133 : ℕ)) / 2 := by
    have h := (log_br_133).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((133 : ℕ)) / 2 ≤ ((12225873/5000000 : ℚ) : ℝ) := by
    have h := (log_br_133).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 237967/625000) (δ := 893/100000000) (ψ := -750661/1000000) 247 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t133 : ((41394916551/10000000000000 : ℚ) : ℝ) ≤ stT247o2 133 := by
  have hc : ((47739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((133 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41394916551/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((47739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c134 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-76901/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((48978397/20000000 : ℚ) : ℝ) ≤ Real.log ((134 : ℕ)) / 2 := by
    have h := (log_br_134).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((134 : ℕ)) / 2 ≤ ((48978399/20000000 : ℚ) : ℝ) := by
    have h := (log_br_134).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6120217/10000000) (δ := 619/50000000) (ψ := -750661/1000000) 247 96
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t134 : ((-33218354657/500000000000 : ℚ) : ℝ) ≤ stT247o2 134 := by
  have hc : ((-38453/50000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((134 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33218354657/500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-38453/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c135 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-487429/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49052747/20000000 : ℚ) : ℝ) ≤ Real.log ((135 : ℕ)) / 2 := by
    have h := (log_br_135).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((135 : ℕ)) / 2 ≤ ((12263187/5000000 : ℚ) : ℝ) := by
    have h := (log_br_135).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7292197/10000000) (δ := 239/25000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t135 : ((-209766811001/2500000000000 : ℚ) : ℝ) ≤ stT247o2 135 := by
  have hc : ((-243727/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((135 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209766811001/2500000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-243727/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c136 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-421083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12281637/5000000 : ℚ) : ℝ) ≤ Real.log ((136 : ℕ)) / 2 := by
    have h := (log_br_136).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((136 : ℕ)) / 2 ≤ ((49126549/20000000 : ℚ) : ℝ) := by
    have h := (log_br_136).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5013589/10000000) (δ := 1041/100000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t136 : ((-361118599569/10000000000000 : ℚ) : ℝ) ≤ stT247o2 136 := by
  have hc : ((-421133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((136 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361118599569/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-421133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c137 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((452999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49199809/20000000 : ℚ) : ℝ) ≤ Real.log ((137 : ℕ)) / 2 := by
    have h := (log_br_137).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((137 : ℕ)) / 2 ≤ ((4919981/2000000 : ℚ) : ℝ) := by
    have h := (log_br_137).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1375837/5000000) (δ := 233/25000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t137 : ((386980148793/10000000000000 : ℚ) : ℝ) ≤ stT247o2 137 := by
  have hc : ((452949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((137 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386980148793/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((452949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c138 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((97957/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6159067/2500000 : ℚ) : ℝ) ≤ Real.log ((138 : ℕ)) / 2 := by
    have h := (log_br_138).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((138 : ℕ)) / 2 ≤ ((49272537/20000000 : ℚ) : ℝ) := by
    have h := (log_br_138).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -50621/1000000) (δ := 1021/100000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t138 : ((325711827/3906250000 : ℚ) : ℝ) ≤ stT247o2 138 := by
  have hc : ((3061/3125 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((138 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((325711827/3906250000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((3061/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c139 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((24117/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49344739/20000000 : ℚ) : ℝ) ≤ Real.log ((139 : ℕ)) / 2 := by
    have h := (log_br_139).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((139 : ℕ)) / 2 ≤ ((2467237/1000000 : ℚ) : ℝ) := by
    have h := (log_br_139).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 861521/5000000) (δ := 421/50000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t139 : ((81817698809/1250000000000 : ℚ) : ℝ) ≤ stT247o2 139 := by
  have hc : ((385847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((139 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81817698809/1250000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((385847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c140 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-3729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6177053/2500000 : ℚ) : ℝ) ≤ Real.log ((140 : ℕ)) / 2 := by
    have h := (log_br_140).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((140 : ℕ)) / 2 ≤ ((1976657/800000 : ℚ) : ℝ) := by
    have h := (log_br_140).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3936313/10000000) (δ := 977/100000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t140 : ((-638768149/2000000000000 : ℚ) : ℝ) ≤ stT247o2 140 := by
  have hc : ((-3779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((140 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638768149/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-3779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c141 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-772479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24743799/10000000 : ℚ) : ℝ) ≤ Real.log ((141 : ℕ)) / 2 := by
    have h := (log_br_141).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((141 : ℕ)) / 2 ≤ ((49487599/20000000 : ℚ) : ℝ) := by
    have h := (log_br_141).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6133831/10000000) (δ := 1091/100000000) (ψ := -750661/1000000) 247 97
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t141 : ((-81323355301/1250000000000 : ℚ) : ℝ) ≤ stT247o2 141 := by
  have hc : ((-772529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((141 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81323355301/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-772529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c142 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-196597/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((4955827/2000000 : ℚ) : ℝ) ≤ Real.log ((142 : ℕ)) / 2 := by
    have h := (log_br_142).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((142 : ℕ)) / 2 ≤ ((49558271/20000000 : ℚ) : ℝ) := by
    have h := (log_br_142).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -462009/625000) (δ := 351/50000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t142 : ((-82494527737/1000000000000 : ℚ) : ℝ) ≤ stT247o2 142 := by
  have hc : ((-196607/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((142 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82494527737/1000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-196607/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c143 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-15511/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24814223/10000000 : ℚ) : ℝ) ≤ Real.log ((143 : ℕ)) / 2 := by
    have h := (log_br_143).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((143 : ℕ)) / 2 ≤ ((49628447/20000000 : ℚ) : ℝ) := by
    have h := (log_br_143).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5225469/10000000) (δ := 7/781250) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t143 : ((-207556348843/5000000000000 : ℚ) : ℝ) ≤ stT247o2 143 := by
  have hc : ((-248201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((143 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207556348843/5000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-248201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c144 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((66931/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((12424533/5000000 : ℚ) : ℝ) ≤ Real.log ((144 : ℕ)) / 2 := by
    have h := (log_br_144).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((144 : ℕ)) / 2 ≤ ((49698133/20000000 : ℚ) : ℝ) := by
    have h := (log_br_144).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -768473/2500000) (δ := 303/25000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t144 : ((55767477693/2000000000000 : ℚ) : ℝ) ≤ stT247o2 144 := by
  have hc : ((66921/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((144 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55767477693/2000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((66921/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c145 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((930551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((49767337/20000000 : ℚ) : ℝ) ≤ Real.log ((145 : ℕ)) / 2 := by
    have h := (log_br_145).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((145 : ℕ)) / 2 ≤ ((24883669/10000000 : ℚ) : ℝ) := by
    have h := (log_br_145).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -187441/2000000) (δ := 721/100000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t145 : ((386369138727/5000000000000 : ℚ) : ℝ) ≤ stT247o2 145 := by
  have hc : ((930501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((145 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386369138727/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((930501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c146 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((889787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24918033/10000000 : ℚ) : ℝ) ≤ Real.log ((146 : ℕ)) / 2 := by
    have h := (log_br_146).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((146 : ℕ)) / 2 ≤ ((49836067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_146).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 296199/2500000) (δ := 249/25000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t146 : ((147270157977/2000000000000 : ℚ) : ℝ) ≤ stT247o2 146 := by
  have hc : ((889737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((146 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147270157977/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((889737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c147 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((251153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1996173/800000 : ℚ) : ℝ) ≤ Real.log ((147 : ℕ)) / 2 := by
    have h := (log_br_147).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((147 : ℕ)) / 2 ≤ ((24952163/10000000 : ℚ) : ℝ) := by
    have h := (log_br_147).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3292313/10000000) (δ := 1057/100000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t147 : ((103553119479/5000000000000 : ℚ) : ℝ) ≤ stT247o2 147 := by
  have hc : ((251103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((147 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103553119479/5000000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((251103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c148 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-550881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((24986061/10000000 : ℚ) : ℝ) ≤ Real.log ((148 : ℕ)) / 2 := by
    have h := (log_br_148).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((148 : ℕ)) / 2 ≤ ((49972123/20000000 : ℚ) : ℝ) := by
    have h := (log_br_148).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5385541/10000000) (δ := 441/50000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t148 : ((-90572505469/2000000000000 : ℚ) : ℝ) ≤ stT247o2 148 := by
  have hc : ((-550931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((148 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90572505469/2000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-550931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c149 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-9879/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50039463/20000000 : ℚ) : ℝ) ≤ Real.log ((149 : ℕ)) / 2 := by
    have h := (log_br_149).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((149 : ℕ)) / 2 ≤ ((6254933/2500000 : ℚ) : ℝ) := by
    have h := (log_br_149).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3732337/5000000) (δ := 1171/100000000) (ψ := -750661/1000000) 247 98
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t149 : ((-505850159/6250000000 : ℚ) : ℝ) ≤ stT247o2 149 := by
  have hc : ((-19759/20000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((149 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-505850159/6250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-19759/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c150 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-391797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3131647/1250000 : ℚ) : ℝ) ≤ Real.log ((150 : ℕ)) / 2 := by
    have h := (log_br_150).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((150 : ℕ)) / 2 ≤ ((50106353/20000000 : ℚ) : ℝ) := by
    have h := (log_br_150).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -386129/625000) (δ := 1163/100000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t150 : ((-159960743767/2500000000000 : ℚ) : ℝ) ≤ stT247o2 150 := by
  have hc : ((-195911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((150 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159960743767/2500000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-195911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c151 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-1246/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25086399/10000000 : ℚ) : ℝ) ≤ Real.log ((151 : ℕ)) / 2 := by
    have h := (log_br_151).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((151 : ℕ)) / 2 ≤ ((50172799/20000000 : ℚ) : ℝ) := by
    have h := (log_br_151).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2063281/5000000) (δ := 161/20000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t151 : ((-32467739733/5000000000000 : ℚ) : ℝ) ≤ stT247o2 151 := by
  have hc : ((-39897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((151 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32467739733/5000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-39897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c152 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((670851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10047761/4000000 : ℚ) : ℝ) ≤ Real.log ((152 : ℕ)) / 2 := by
    have h := (log_br_152).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((152 : ℕ)) / 2 ≤ ((25119403/10000000 : ℚ) : ℝ) := by
    have h := (log_br_152).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2088601/10000000) (δ := 101/10000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t152 : ((544091386707/10000000000000 : ℚ) : ℝ) ≤ stT247o2 152 := by
  have hc : ((670801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((152 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544091386707/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((670801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c153 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((124959/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50304379/20000000 : ℚ) : ℝ) ≤ Real.log ((153 : ℕ)) / 2 := by
    have h := (log_br_153).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((153 : ℕ)) / 2 ≤ ((2515219/1000000 : ℚ) : ℝ) := by
    have h := (log_br_153).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -64003/10000000) (δ := 49/5000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t153 : ((101018300643/1250000000000 : ℚ) : ℝ) ≤ stT247o2 153 := by
  have hc : ((499811/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((153 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101018300643/1250000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((499811/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c154 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((711643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25184763/10000000 : ℚ) : ℝ) ≤ Real.log ((154 : ℕ)) / 2 := by
    have h := (log_br_154).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((154 : ℕ)) / 2 ≤ ((50369527/20000000 : ℚ) : ℝ) := by
    have h := (log_br_154).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 486851/2500000) (δ := 249/20000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t154 : ((286708647223/5000000000000 : ℚ) : ℝ) ≤ stT247o2 154 := by
  have hc : ((711593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((154 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((286708647223/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((711593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c155 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-7521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50434251/20000000 : ℚ) : ℝ) ≤ Real.log ((155 : ℕ)) / 2 := by
    have h := (log_br_155).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((155 : ℕ)) / 2 ≤ ((12608563/5000000 : ℚ) : ℝ) := by
    have h := (log_br_155).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3945793/10000000) (δ := 53/5000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t155 : ((-304058931/500000000000 : ℚ) : ℝ) ≤ stT247o2 155 := by
  have hc : ((-7571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((155 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-304058931/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-7571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c156 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-143713/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((39452/15625 : ℚ) : ℝ) ≤ Real.log ((156 : ℕ)) / 2 := by
    have h := (log_br_156).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((156 : ℕ)) / 2 ≤ ((50498561/20000000 : ℚ) : ℝ) := by
    have h := (log_br_156).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5931331/10000000) (δ := 231/20000000) (ψ := -750661/1000000) 247 99
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t156 : ((-115070526443/2000000000000 : ℚ) : ℝ) ≤ stT247o2 156 := by
  have hc : ((-143723/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((156 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115070526443/2000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-143723/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c157 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-499899/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25281229/10000000 : ℚ) : ℝ) ≤ Real.log ((157 : ℕ)) / 2 := by
    have h := (log_br_157).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((157 : ℕ)) / 2 ≤ ((50562459/20000000 : ℚ) : ℝ) := by
    have h := (log_br_157).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3901891/5000000) (δ := 47/4000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t157 : ((-99745711347/1250000000000 : ℚ) : ℝ) ≤ stT247o2 157 := by
  have hc : ((-124981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((157 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99745711347/1250000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-124981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c158 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-693681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1012519/400000 : ℚ) : ℝ) ≤ Real.log ((158 : ℕ)) / 2 := by
    have h := (log_br_158).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((158 : ℕ)) / 2 ≤ ((50625951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_158).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2921729/5000000) (δ := 167/20000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t158 : ((-275951623449/5000000000000 : ℚ) : ℝ) ≤ stT247o2 158 := by
  have hc : ((-693731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((158 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275951623449/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-693731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c159 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((2519/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25344521/10000000 : ℚ) : ℝ) ≤ Real.log ((159 : ℕ)) / 2 := by
    have h := (log_br_159).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((159 : ℕ)) / 2 ≤ ((50689043/20000000 : ℚ) : ℝ) := by
    have h := (log_br_159).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1947751/5000000) (δ := 243/20000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t159 : ((1989764959/2000000000000 : ℚ) : ℝ) ≤ stT247o2 159 := by
  have hc : ((2509/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((159 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1989764959/2000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((2509/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c160 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((708163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25375869/10000000 : ℚ) : ℝ) ≤ Real.log ((160 : ℕ)) / 2 := by
    have h := (log_br_160).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((160 : ℕ)) / 2 ≤ ((50751739/20000000 : ℚ) : ℝ) := by
    have h := (log_br_160).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1959759/10000000) (δ := 211/20000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t160 : ((559812186297/10000000000000 : ℚ) : ℝ) ≤ stT247o2 160 := by
  have hc : ((708113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((160 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((559812186297/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((708113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c161 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((124987/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50814043/20000000 : ℚ) : ℝ) ≤ Real.log ((161 : ℕ)) / 2 := by
    have h := (log_br_161).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((161 : ℕ)) / 2 ≤ ((12703511/5000000 : ℚ) : ℝ) := by
    have h := (log_br_161).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -36077/10000000) (δ := 197/25000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t161 : ((39399431553/500000000000 : ℚ) : ℝ) ≤ stT247o2 161 := by
  have hc : ((499923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((161 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39399431553/500000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((499923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c162 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((1463/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((50875963/20000000 : ℚ) : ℝ) ≤ Real.log ((162 : ℕ)) / 2 := by
    have h := (log_br_162).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((162 : ℕ)) / 2 ≤ ((12718991/5000000 : ℚ) : ℝ) := by
    have h := (log_br_162).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 937847/5000000) (δ := 81/10000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t162 : ((5746812473/100000000000 : ℚ) : ℝ) ≤ stT247o2 162 := by
  have hc : ((14629/20000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((162 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5746812473/100000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((14629/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c163 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((60479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25468751/10000000 : ℚ) : ℝ) ≤ Real.log ((163 : ℕ)) / 2 := by
    have h := (log_br_163).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((163 : ℕ)) / 2 ≤ ((50937503/20000000 : ℚ) : ℝ) := by
    have h := (log_br_163).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 37757/100000) (δ := 247/20000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t163 : ((2366580927/500000000000 : ℚ) : ℝ) ≤ stT247o2 163 := by
  have hc : ((60429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((163 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2366580927/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((60429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c164 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-640261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6374833/2500000 : ℚ) : ℝ) ≤ Real.log ((164 : ℕ)) / 2 := by
    have h := (log_br_164).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((164 : ℕ)) / 2 ≤ ((10199733/4000000 : ℚ) : ℝ) := by
    have h := (log_br_164).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1132817/2000000) (δ := 181/20000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t164 : ((-499999010259/10000000000000 : ℚ) : ℝ) ≤ stT247o2 164 := by
  have hc : ((-640311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((164 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-499999010259/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-640311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c165 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-992173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25529727/10000000 : ℚ) : ℝ) ≤ Real.log ((165 : ℕ)) / 2 := by
    have h := (log_br_165).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((165 : ℕ)) / 2 ≤ ((10211891/4000000 : ℚ) : ℝ) := by
    have h := (log_br_165).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 754099/1000000) (δ := 883/100000000) (ψ := -750661/1000000) 247 100
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t165 : ((-772444613277/10000000000000 : ℚ) : ℝ) ≤ stT247o2 165 := by
  have hc : ((-992223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((165 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772444613277/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-992223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c166 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-5083/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51119877/20000000 : ℚ) : ℝ) ≤ Real.log ((166 : ℕ)) / 2 := by
    have h := (log_br_166).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((166 : ℕ)) / 2 ≤ ((25559939/10000000 : ℚ) : ℝ) := by
    have h := (log_br_166).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -196919/312500) (δ := 1089/100000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t166 : ((-63126689283/1000000000000 : ℚ) : ℝ) ≤ stT247o2 166 := by
  have hc : ((-81333/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((166 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63126689283/1000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-81333/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c167 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-103263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25589969/10000000 : ℚ) : ℝ) ≤ Real.log ((167 : ℕ)) / 2 := by
    have h := (log_br_167).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((167 : ℕ)) / 2 ≤ ((51179939/20000000 : ℚ) : ℝ) := by
    have h := (log_br_167).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -555881/1250000) (δ := 271/25000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t167 : ((-156106901/9765625000 : ℚ) : ℝ) ≤ stT247o2 167 := by
  have hc : ((-12911/62500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((167 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156106901/9765625000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-12911/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c168 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((504923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51239639/20000000 : ℚ) : ℝ) ≤ Real.log ((168 : ℕ)) / 2 := by
    have h := (log_br_168).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((168 : ℕ)) / 2 ≤ ((1280991/500000 : ℚ) : ℝ) := by
    have h := (log_br_168).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2603759/10000000) (δ := 979/100000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t168 : ((97379399367/2500000000000 : ℚ) : ℝ) ≤ stT247o2 168 := by
  have hc : ((504873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((168 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97379399367/2500000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((504873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c169 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((952771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51298987/20000000 : ℚ) : ℝ) ≤ Real.log ((169 : ℕ)) / 2 := by
    have h := (log_br_169).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((169 : ℕ)) / 2 ≤ ((12824747/5000000 : ℚ) : ℝ) := by
    have h := (log_br_169).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -77141/1000000) (δ := 1079/100000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t169 : ((73286157483/1000000000000 : ℚ) : ℝ) ≤ stT247o2 169 := by
  have hc : ((952721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((169 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73286157483/1000000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((952721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c170 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((228267/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1604937/625000 : ℚ) : ℝ) ≤ Real.log ((170 : ℕ)) / 2 := by
    have h := (log_br_170).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((170 : ℕ)) / 2 ≤ ((10271597/4000000 : ℚ) : ℝ) := by
    have h := (log_br_170).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1050129/10000000) (δ := 407/50000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t170 : ((87531492169/1250000000000 : ℚ) : ℝ) ≤ stT247o2 170 := by
  have hc : ((456509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((170 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87531492169/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((456509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c171 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((206799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10283327/4000000 : ℚ) : ℝ) ≤ Real.log ((171 : ℕ)) / 2 := by
    have h := (log_br_171).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((171 : ℕ)) / 2 ≤ ((12854159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_171).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 572197/2000000) (δ := 679/100000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t171 : ((79062003253/2500000000000 : ℚ) : ℝ) ≤ stT247o2 171 := by
  have hc : ((103387/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((171 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79062003253/2500000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((103387/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c172 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-36189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((201074/78125 : ℚ) : ℝ) ≤ Real.log ((172 : ℕ)) / 2 := by
    have h := (log_br_172).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((172 : ℕ)) / 2 ≤ ((10294989/4000000 : ℚ) : ℝ) := by
    have h := (log_br_172).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2330641/5000000) (δ := 59/6250000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t172 : ((-110394499033/5000000000000 : ℚ) : ℝ) ≤ stT247o2 172 := by
  have hc : ((-144781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((172 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110394499033/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-144781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c173 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-846651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10306583/4000000 : ℚ) : ℝ) ≤ Real.log ((173 : ℕ)) / 2 := by
    have h := (log_br_173).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((173 : ℕ)) / 2 ≤ ((12883229/5000000 : ℚ) : ℝ) := by
    have h := (log_br_173).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3225571/5000000) (δ := 1159/100000000) (ψ := -750661/1000000) 247 101
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t173 : ((-321867458243/5000000000000 : ℚ) : ℝ) ≤ stT247o2 173 := by
  have hc : ((-846701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((173 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321867458243/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-846701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c174 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-988669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6448819/2500000 : ℚ) : ℝ) ≤ Real.log ((174 : ℕ)) / 2 := by
    have h := (log_br_174).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((174 : ℕ)) / 2 ≤ ((51590553/20000000 : ℚ) : ℝ) := by
    have h := (log_br_174).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3738639/5000000) (δ := 239/20000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t174 : ((-749546885181/10000000000000 : ℚ) : ℝ) ≤ stT247o2 174 := by
  have hc : ((-988719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((174 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-749546885181/10000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-988719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c175 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-326817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51647859/20000000 : ℚ) : ℝ) ≤ Real.log ((175 : ℕ)) / 2 := by
    have h := (log_br_175).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((175 : ℕ)) / 2 ≤ ((2582393/1000000 : ℚ) : ℝ) := by
    have h := (log_br_175).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1426983/2500000) (δ := 89/10000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t175 : ((-123534673109/2500000000000 : ℚ) : ℝ) ≤ stT247o2 175 := by
  have hc : ((-163421/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((175 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123534673109/2500000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-163421/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c176 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-8671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51704839/20000000 : ℚ) : ℝ) ≤ Real.log ((176 : ℕ)) / 2 := by
    have h := (log_br_176).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((176 : ℕ)) / 2 ≤ ((1292621/500000 : ℚ) : ℝ) := by
    have h := (log_br_176).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -987167/2500000) (δ := 23/2000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t176 : ((-6573706659/10000000000000 : ℚ) : ℝ) ≤ stT247o2 176 := by
  have hc : ((-8721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((176 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6573706659/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-8721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c177 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((127469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((51761497/20000000 : ℚ) : ℝ) ≤ Real.log ((177 : ℕ)) / 2 := by
    have h := (log_br_177).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((177 : ℕ)) / 2 ≤ ((25880749/10000000 : ℚ) : ℝ) := by
    have h := (log_br_177).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2199371/10000000) (δ := 419/50000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t177 : ((47902023757/1000000000000 : ℚ) : ℝ) ≤ stT247o2 177 := by
  have hc : ((127459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((177 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47902023757/1000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((127459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c178 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((1573/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10363567/4000000 : ℚ) : ℝ) ≤ Real.log ((178 : ℕ)) / 2 := by
    have h := (log_br_178).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((178 : ℕ)) / 2 ≤ ((12954459/5000000 : ℚ) : ℝ) := by
    have h := (log_br_178).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -45993/1000000) (δ := 157/25000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t178 : ((29473807513/400000000000 : ℚ) : ℝ) ≤ stT247o2 178 := by
  have hc : ((39323/40000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((178 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29473807513/400000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((39323/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c179 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((174753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((25936929/10000000 : ℚ) : ℝ) ≤ Real.log ((179 : ℕ)) / 2 := by
    have h := (log_br_179).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((179 : ℕ)) / 2 ≤ ((51873859/20000000 : ℚ) : ℝ) := by
    have h := (log_br_179).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 634883/5000000) (δ := 1193/100000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t179 : ((26121806841/400000000000 : ℚ) : ℝ) ≤ stT247o2 179 := by
  have hc : ((174743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((179 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26121806841/400000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((174743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c180 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((91537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1622799/625000 : ℚ) : ℝ) ≤ Real.log ((180 : ℕ)) / 2 := by
    have h := (log_br_180).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((180 : ℕ)) / 2 ≤ ((51929569/20000000 : ℚ) : ℝ) := by
    have h := (log_br_180).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1494913/5000000) (δ := 643/100000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t180 : ((27287297479/1000000000000 : ℚ) : ℝ) ≤ stT247o2 180 := by
  have hc : ((183049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((180 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27287297479/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((183049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c181 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-76109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5198497/2000000 : ℚ) : ℝ) ≤ Real.log ((181 : ℕ)) / 2 := by
    have h := (log_br_181).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((181 : ℕ)) / 2 ≤ ((51984971/20000000 : ℚ) : ℝ) := by
    have h := (log_br_181).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4700357/10000000) (δ := 873/100000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t181 : ((-22632292137/1000000000000 : ℚ) : ℝ) ≤ stT247o2 181 := by
  have hc : ((-152243/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((181 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22632292137/1000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-152243/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c182 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-83591/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26020033/10000000 : ℚ) : ℝ) ≤ Real.log ((182 : ℕ)) / 2 := by
    have h := (log_br_182).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((182 : ℕ)) / 2 ≤ ((52040067/20000000 : ℚ) : ℝ) := by
    have h := (log_br_182).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6401463/10000000) (δ := 209/20000000) (ψ := -750661/1000000) 247 102
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t182 : ((-12393107/200000000 : ℚ) : ℝ) ≤ stT247o2 182 := by
  have hc : ((-20899/25000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((182 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12393107/200000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-20899/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c183 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-31107/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52094861/20000000 : ℚ) : ℝ) ≤ Real.log ((183 : ℕ)) / 2 := by
    have h := (log_br_183).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((183 : ℕ)) / 2 ≤ ((26047431/10000000 : ℚ) : ℝ) := by
    have h := (log_br_183).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1522943/2000000) (δ := 63/10000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t183 : ((-183969070307/2500000000000 : ℚ) : ℝ) ≤ stT247o2 183 := by
  have hc : ((-497737/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((183 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183969070307/2500000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-497737/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c184 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-89849/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52149357/20000000 : ℚ) : ℝ) ≤ Real.log ((184 : ℕ)) / 2 := by
    have h := (log_br_184).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((184 : ℕ)) / 2 ≤ ((26074679/10000000 : ℚ) : ℝ) := by
    have h := (log_br_184).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5932149/10000000) (δ := 71/10000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t184 : ((-26496875541/500000000000 : ℚ) : ℝ) ≤ stT247o2 184 := by
  have hc : ((-359421/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((184 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26496875541/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-359421/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c185 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-16537/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26101779/10000000 : ℚ) : ℝ) ≤ Real.log ((185 : ℕ)) / 2 := by
    have h := (log_br_185).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((185 : ℕ)) / 2 ≤ ((52203559/20000000 : ℚ) : ℝ) := by
    have h := (log_br_185).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -266169/625000) (δ := 963/100000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t185 : ((-9730276439/1000000000000 : ℚ) : ℝ) ≤ stT247o2 185 := by
  have hc : ((-66173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((185 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9730276439/1000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-66173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c186 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((15881/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26128733/10000000 : ℚ) : ℝ) ≤ Real.log ((186 : ℕ)) / 2 := by
    have h := (log_br_186).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((186 : ℕ)) / 2 ≤ ((52257467/20000000 : ℚ) : ℝ) := by
    have h := (log_br_186).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2594279/10000000) (δ := 179/20000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t186 : ((37258749937/1000000000000 : ℚ) : ℝ) ≤ stT247o2 186 := by
  have hc : ((254071/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((186 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37258749937/1000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((254071/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c187 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((11629/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26155543/10000000 : ℚ) : ℝ) ≤ Real.log ((187 : ℕ)) / 2 := by
    have h := (log_br_187).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((187 : ℕ)) / 2 ≤ ((52311087/20000000 : ℚ) : ℝ) := by
    have h := (log_br_187).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -938779/10000000) (δ := 1043/100000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t187 : ((8503505043/125000000000 : ℚ) : ℝ) ≤ stT247o2 187 := by
  have hc : ((93027/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((187 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8503505043/125000000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((93027/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c188 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((480089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52364419/20000000 : ℚ) : ℝ) ≤ Real.log ((188 : ℕ)) / 2 := by
    have h := (log_br_188).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((188 : ℕ)) / 2 ≤ ((2618221/1000000 : ℚ) : ℝ) := by
    have h := (log_br_188).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 707891/10000000) (δ := 37/5000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t188 : ((1367664831/19531250000 : ℚ) : ℝ) ≤ stT247o2 188 := by
  have hc : ((15002/15625 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((188 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1367664831/19531250000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((15002/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c189 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((18473/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5241747/2000000 : ℚ) : ℝ) ≤ Real.log ((189 : ℕ)) / 2 := by
    have h := (log_br_189).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((189 : ℕ)) / 2 ≤ ((52417471/20000000 : ℚ) : ℝ) := by
    have h := (log_br_189).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1172913/5000000) (δ := 1083/100000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t189 : ((6717987933/156250000000 : ℚ) : ℝ) ≤ stT247o2 189 := by
  have hc : ((295543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((189 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6717987933/156250000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((295543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c190 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-77/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((327939/125000 : ℚ) : ℝ) ≤ Real.log ((190 : ℕ)) / 2 := by
    have h := (log_br_190).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((190 : ℕ)) / 2 ≤ ((52470241/20000000 : ℚ) : ℝ) := by
    have h := (log_br_190).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1987559/5000000) (δ := 177/20000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t190 : ((-140017061/100000000000 : ℚ) : ℝ) ≤ stT247o2 190 := by
  have hc : ((-193/10000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((190 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-140017061/100000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-193/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c191 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-619061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26261367/10000000 : ℚ) : ℝ) ≤ Real.log ((191 : ℕ)) / 2 := by
    have h := (log_br_191).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((191 : ℕ)) / 2 ≤ ((10504547/4000000 : ℚ) : ℝ) := by
    have h := (log_br_191).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 349741/625000) (δ := 923/100000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t191 : ((-17918929673/400000000000 : ℚ) : ℝ) ≤ stT247o2 191 := by
  have hc : ((-619111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((191 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17918929673/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-619111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c192 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-193363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52574953/20000000 : ℚ) : ℝ) ≤ Real.log ((192 : ℕ)) / 2 := by
    have h := (log_br_192).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((192 : ℕ)) / 2 ≤ ((26287477/10000000 : ℚ) : ℝ) := by
    have h := (log_br_192).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1802033/2500000) (δ := 89/10000000) (ψ := -750661/1000000) 247 103
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t192 : ((-17444371703/250000000000 : ℚ) : ℝ) ≤ stT247o2 192 := by
  have hc : ((-193373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((192 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17444371703/250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-193373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c193 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-463733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52626901/20000000 : ℚ) : ℝ) ≤ Real.log ((193 : ℕ)) / 2 := by
    have h := (log_br_193).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((193 : ℕ)) / 2 ≤ ((26313451/10000000 : ℚ) : ℝ) := by
    have h := (log_br_193).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1723983/2500000) (δ := 1081/100000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t193 : ((-20863776783/312500000000 : ℚ) : ℝ) ≤ stT247o2 193 := by
  have hc : ((-231879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((193 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20863776783/312500000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-231879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c194 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-261059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52678581/20000000 : ℚ) : ℝ) ≤ Real.log ((194 : ℕ)) / 2 := by
    have h := (log_br_194).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((194 : ℕ)) / 2 ≤ ((26339291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_194).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5300321/10000000) (δ := 721/100000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t194 : ((-46861901889/1250000000000 : ℚ) : ℝ) ≤ stT247o2 194 := by
  have hc : ((-65271/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((194 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46861901889/1250000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-65271/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c195 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((42763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10545999/4000000 : ℚ) : ℝ) ≤ Real.log ((195 : ℕ)) / 2 := by
    have h := (log_br_195).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((195 : ℕ)) / 2 ≤ ((13182499/5000000 : ℚ) : ℝ) := by
    have h := (log_br_195).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1856457/5000000) (δ := 711/100000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t195 : ((7651320033/1250000000000 : ℚ) : ℝ) ≤ stT247o2 195 := by
  have hc : ((21369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((195 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7651320033/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((21369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c196 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((657387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26390573/10000000 : ℚ) : ℝ) ≤ Real.log ((196 : ℕ)) / 2 := by
    have h := (log_br_196).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((196 : ℕ)) / 2 ≤ ((52781147/20000000 : ℚ) : ℝ) := by
    have h := (log_br_196).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2133627/10000000) (δ := 353/50000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t196 : ((93905191809/2000000000000 : ℚ) : ℝ) ≤ stT247o2 196 := by
  have hc : ((657337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((196 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93905191809/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((657337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c197 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((194961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52832037/20000000 : ℚ) : ℝ) ≤ Real.log ((197 : ℕ)) / 2 := by
    have h := (log_br_197).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((197 : ℕ)) / 2 ≤ ((26416019/10000000 : ℚ) : ℝ) := by
    have h := (log_br_197).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -562377/10000000) (δ := 917/100000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t197 : ((13889673897/200000000000 : ℚ) : ℝ) ≤ stT247o2 197 := by
  have hc : ((194951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((197 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13889673897/200000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((194951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c198 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((460459/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((5288267/2000000 : ℚ) : ℝ) ≤ Real.log ((198 : ℕ)) / 2 := by
    have h := (log_br_198).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((198 : ℕ)) / 2 ≤ ((52882671/20000000 : ℚ) : ℝ) := by
    have h := (log_br_198).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 500459/5000000) (δ := 109/12500000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t198 : ((163608085173/2500000000000 : ℚ) : ℝ) ≤ stT247o2 198 := by
  have hc : ((230217/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((198 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163608085173/2500000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((230217/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c199 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((130301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((6616631/2500000 : ℚ) : ℝ) ≤ Real.log ((199 : ℕ)) / 2 := by
    have h := (log_br_199).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((199 : ℕ)) / 2 ≤ ((52933049/20000000 : ℚ) : ℝ) := by
    have h := (log_br_199).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2556337/10000000) (δ := 471/50000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t199 : ((184718084337/5000000000000 : ℚ) : ℝ) ≤ stT247o2 199 := by
  have hc : ((260577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((199 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184718084337/5000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((260577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c200 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-8841/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((52983173/20000000 : ℚ) : ℝ) ≤ Real.log ((200 : ℕ)) / 2 := by
    have h := (log_br_200).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((200 : ℕ)) / 2 ≤ ((26491587/10000000 : ℚ) : ℝ) := by
    have h := (log_br_200).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4103959/10000000) (δ := 801/100000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t200 : ((-25023809623/5000000000000 : ℚ) : ℝ) ≤ stT247o2 200 := by
  have hc : ((-35389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((200 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25023809623/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-35389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c201 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-317013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53033049/20000000 : ℚ) : ℝ) ≤ Real.log ((201 : ℕ)) / 2 := by
    have h := (log_br_201).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((201 : ℕ)) / 2 ≤ ((1060661/400000 : ℚ) : ℝ) := by
    have h := (log_br_201).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2821931/5000000) (δ := 1177/100000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t201 : ((-55905371287/1250000000000 : ℚ) : ℝ) ≤ stT247o2 201 := by
  have hc : ((-158519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((201 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55905371287/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-158519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c202 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-192693/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13270669/5000000 : ℚ) : ℝ) ≤ Real.log ((202 : ℕ)) / 2 := by
    have h := (log_br_202).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((202 : ℕ)) / 2 ≤ ((53082677/20000000 : ℚ) : ℝ) := by
    have h := (log_br_202).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1794031/2500000) (δ := 299/25000000) (ψ := -750661/1000000) 247 104
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t202 : ((-67792722697/1000000000000 : ℚ) : ℝ) ≤ stT247o2 202 := by
  have hc : ((-192703/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((202 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67792722697/1000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-192703/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c203 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-117897/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53132059/20000000 : ℚ) : ℝ) ≤ Real.log ((203 : ℕ)) / 2 := by
    have h := (log_br_203).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((203 : ℕ)) / 2 ≤ ((2656603/1000000 : ℚ) : ℝ) := by
    have h := (log_br_203).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1401429/2000000) (δ := 481/50000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t203 : ((-331007715019/5000000000000 : ℚ) : ℝ) ≤ stT247o2 203 := by
  have hc : ((-471613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((203 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331007715019/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-471613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c204 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-146311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53181199/20000000 : ℚ) : ℝ) ≤ Real.log ((204 : ℕ)) / 2 := by
    have h := (log_br_204).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((204 : ℕ)) / 2 ≤ ((132953/50000 : ℚ) : ℝ) := by
    have h := (log_br_204).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5489943/10000000) (δ := 571/50000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t204 : ((-204894163227/5000000000000 : ℚ) : ℝ) ≤ stT247o2 204 := by
  have hc : ((-292647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((204 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204894163227/5000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-292647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c205 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-10633/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53230099/20000000 : ℚ) : ℝ) ≤ Real.log ((205 : ℕ)) / 2 := by
    have h := (log_br_205).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((205 : ℕ)) / 2 ≤ ((532301/200000 : ℚ) : ℝ) := by
    have h := (log_br_205).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -6219/15625) (δ := 481/50000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t205 : ((-3721938799/2500000000000 : ℚ) : ℝ) ≤ stT247o2 205 := by
  have hc : ((-5329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((205 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3721938799/2500000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-5329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c206 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((547779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53278761/20000000 : ℚ) : ℝ) ≤ Real.log ((206 : ℕ)) / 2 := by
    have h := (log_br_206).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((206 : ℕ)) / 2 ≤ ((26639381/10000000 : ℚ) : ℝ) := by
    have h := (log_br_206).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -619431/2500000) (δ := 13/1562500) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t206 : ((381620869357/10000000000000 : ℚ) : ℝ) ≤ stT247o2 206 := by
  have hc : ((547729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((206 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381620869357/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((547729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c207 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((184751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53327187/20000000 : ℚ) : ℝ) ≤ Real.log ((207 : ℕ)) / 2 := by
    have h := (log_br_207).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((207 : ℕ)) / 2 ≤ ((13331797/5000000 : ℚ) : ℝ) := by
    have h := (log_br_207).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -245641/2500000) (δ := 561/50000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t207 : ((16050482821/250000000000 : ℚ) : ℝ) ≤ stT247o2 207 := by
  have hc : ((184741/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((207 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16050482821/250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((184741/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c208 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((244909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2668769/1000000 : ℚ) : ℝ) ≤ Real.log ((208 : ℕ)) / 2 := by
    have h := (log_br_208).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((208 : ℕ)) / 2 ≤ ((53375381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_208).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 505391/10000000) (δ := 967/100000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t208 : ((2716881771/40000000000 : ℚ) : ℝ) ≤ stT247o2 208 := by
  have hc : ((489793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((208 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2716881771/40000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((489793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c209 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((700653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26711671/10000000 : ℚ) : ℝ) ≤ Real.log ((209 : ℕ)) / 2 := by
    have h := (log_br_209).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((209 : ℕ)) / 2 ≤ ((53423343/20000000 : ℚ) : ℝ) := by
    have h := (log_br_209).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1986209/10000000) (δ := 621/100000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t209 : ((242308451771/5000000000000 : ℚ) : ℝ) ≤ stT247o2 209 := by
  have hc : ((700603/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((209 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242308451771/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((700603/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c210 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((2902/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2138843/800000 : ℚ) : ℝ) ≤ Real.log ((210 : ℕ)) / 2 := by
    have h := (log_br_210).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((210 : ℕ)) / 2 ≤ ((13367769/5000000 : ℚ) : ℝ) := by
    have h := (log_br_210).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 3459959/10000000) (δ := 219/25000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t210 : ((12812988907/1000000000000 : ℚ) : ℝ) ≤ stT247o2 210 := by
  have hc : ((92839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((210 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12812988907/1000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((92839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c211 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-194657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53518581/20000000 : ℚ) : ℝ) ≤ Real.log ((211 : ℕ)) / 2 := by
    have h := (log_br_211).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((211 : ℕ)) / 2 ≤ ((26759291/10000000 : ℚ) : ℝ) := by
    have h := (log_br_211).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1231677/2500000) (δ := 413/50000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t211 : ((-67012367289/2500000000000 : ℚ) : ℝ) ≤ stT247o2 211 := by
  have hc : ((-97341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((211 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67012367289/2500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-97341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c212 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-166523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((26782931/10000000 : ℚ) : ℝ) ≤ Real.log ((212 : ℕ)) / 2 := by
    have h := (log_br_212).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((212 : ℕ)) / 2 ≤ ((53565863/20000000 : ℚ) : ℝ) := by
    have h := (log_br_212).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 6386521/10000000) (δ := 897/100000000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t212 : ((-114375363999/2000000000000 : ℚ) : ℝ) ≤ stT247o2 212 := by
  have hc : ((-166533/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((212 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114375363999/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-166533/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c213 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-999983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53612921/20000000 : ℚ) : ℝ) ≤ Real.log ((213 : ℕ)) / 2 := by
    have h := (log_br_213).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((213 : ℕ)) / 2 ≤ ((26806461/10000000 : ℚ) : ℝ) := by
    have h := (log_br_213).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1567893/2000000) (δ := 99/12500000) (ψ := -750661/1000000) 247 105
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t213 : ((-685211611237/10000000000000 : ℚ) : ℝ) ≤ stT247o2 213 := by
  have hc : ((-1000033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((213 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685211611237/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-1000033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c214 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-840469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((670747/250000 : ℚ) : ℝ) ≤ Real.log ((214 : ℕ)) / 2 := by
    have h := (log_br_214).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((214 : ℕ)) / 2 ≤ ((53659761/20000000 : ℚ) : ℝ) := by
    have h := (log_br_214).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -160559/250000) (δ := 27/2500000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t214 : ((-287283510567/5000000000000 : ℚ) : ℝ) ≤ stT247o2 214 := by
  have hc : ((-840519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((214 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-287283510567/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-840519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c215 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-409941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2685319/1000000 : ℚ) : ℝ) ≤ Real.log ((215 : ℕ)) / 2 := by
    have h := (log_br_215).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((215 : ℕ)) / 2 ≤ ((53706381/20000000 : ℚ) : ℝ) := by
    have h := (log_br_215).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -4982963/10000000) (δ := 9/1000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t215 : ((-55922362409/2000000000000 : ℚ) : ℝ) ≤ stT247o2 215 := by
  have hc : ((-409991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((215 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55922362409/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-409991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c216 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((9383/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3359549/1250000 : ℚ) : ℝ) ≤ Real.log ((216 : ℕ)) / 2 := by
    have h := (log_br_216).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((216 : ℕ)) / 2 ≤ ((10750557/4000000 : ℚ) : ℝ) := by
    have h := (log_br_216).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1775123/5000000) (δ := 29/2500000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t216 : ((51057511107/5000000000000 : ℚ) : ℝ) ≤ stT247o2 216 := by
  have hc : ((75039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((216 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51057511107/5000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((75039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c217 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((8253/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53798973/20000000 : ℚ) : ℝ) ≤ Real.log ((217 : ℕ)) / 2 := by
    have h := (log_br_217).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((217 : ℕ)) / 2 ≤ ((26899487/10000000 : ℚ) : ℝ) := by
    have h := (log_br_217).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1062073/5000000) (δ := 663/100000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t217 : ((11204150509/250000000000 : ℚ) : ℝ) ≤ stT247o2 217 := by
  have hc : ((66019/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((217 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11204150509/250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((66019/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c218 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((192109/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((1076899/400000 : ℚ) : ℝ) ≤ Real.log ((218 : ℕ)) / 2 := by
    have h := (log_br_218).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((218 : ℕ)) / 2 ≤ ((53844951/20000000 : ℚ) : ℝ) := by
    have h := (log_br_218).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -176151/2500000) (δ := 187/25000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t218 : ((26021154243/400000000000 : ℚ) : ℝ) ≤ stT247o2 218 := by
  have hc : ((192099/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((218 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26021154243/400000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((192099/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c219 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((960117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53890717/20000000 : ℚ) : ℝ) ≤ Real.log ((219 : ℕ)) / 2 := by
    have h := (log_br_219).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((219 : ℕ)) / 2 ≤ ((26945359/10000000 : ℚ) : ℝ) := by
    have h := (log_br_219).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 354221/5000000) (δ := 179/20000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t219 : ((648752794379/10000000000000 : ℚ) : ℝ) ≤ stT247o2 219 := by
  have hc : ((960067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((219 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((648752794379/10000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((960067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c220 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((82871/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2157451/800000 : ℚ) : ℝ) ≤ Real.log ((220 : ℕ)) / 2 := by
    have h := (log_br_220).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((220 : ℕ)) / 2 ≤ ((13484069/5000000 : ℚ) : ℝ) := by
    have h := (log_br_220).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2115051/10000000) (δ := 133/20000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t220 : ((223469326341/5000000000000 : ℚ) : ℝ) ≤ stT247o2 220 := by
  have hc : ((331459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((220 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223469326341/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((331459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c221 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((163941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((53981627/20000000 : ℚ) : ℝ) ≤ Real.log ((221 : ℕ)) / 2 := by
    have h := (log_br_221).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((221 : ℕ)) / 2 ≤ ((13495407/5000000 : ℚ) : ℝ) := by
    have h := (log_br_221).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 43941/125000) (δ := 49/4000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t221 : ((3445152711/312500000000 : ℚ) : ℝ) ≤ stT247o2 221 := by
  have hc : ((163891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((221 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3445152711/312500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((163891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c222 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-382849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54026773/20000000 : ℚ) : ℝ) ≤ Real.log ((222 : ℕ)) / 2 := by
    have h := (log_br_222).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((222 : ℕ)) / 2 ≤ ((27013387/10000000 : ℚ) : ℝ) := by
    have h := (log_br_222).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 4909187/10000000) (δ := 983/100000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t222 : ((-256985344143/10000000000000 : ℚ) : ℝ) ≤ stT247o2 222 := by
  have hc : ((-382899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((222 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256985344143/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-382899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c223 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-812213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54071717/20000000 : ℚ) : ℝ) ≤ Real.log ((223 : ℕ)) / 2 := by
    have h := (log_br_223).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((223 : ℕ)) / 2 ≤ ((27035859/10000000 : ℚ) : ℝ) := by
    have h := (log_br_223).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 629683/1000000) (δ := 863/100000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t223 : ((-10878638359/200000000000 : ℚ) : ℝ) ≤ stT247o2 223 := by
  have hc : ((-812263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((223 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10878638359/200000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-812263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c224 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-997531/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2705823/1000000 : ℚ) : ℝ) ≤ Real.log ((224 : ℕ)) / 2 := by
    have h := (log_br_224).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((224 : ℕ)) / 2 ≤ ((54116461/20000000 : ℚ) : ℝ) := by
    have h := (log_br_224).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 959783/1250000) (δ := 31/5000000) (ψ := -750661/1000000) 247 106
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t224 : ((-333268867737/5000000000000 : ℚ) : ℝ) ≤ stT247o2 224 := by
  have hc : ((-997581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((224 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333268867737/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-997581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c225 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-221769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((13540251/5000000 : ℚ) : ℝ) ≤ Real.log ((225 : ℕ)) / 2 := by
    have h := (log_br_225).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((225 : ℕ)) / 2 ≤ ((10832201/4000000 : ℚ) : ℝ) := by
    have h := (log_br_225).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3327209/5000000) (δ := 121/10000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t225 : ((-295708814521/5000000000000 : ℚ) : ℝ) ≤ stT247o2 225 := by
  have hc : ((-443563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((225 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295708814521/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-443563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c226 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-258481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54205349/20000000 : ℚ) : ℝ) ≤ Real.log ((226 : ℕ)) / 2 := by
    have h := (log_br_226).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((226 : ℕ)) / 2 ≤ ((54205351/20000000 : ℚ) : ℝ) := by
    have h := (log_br_226).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -5285237/10000000) (δ := 1/78125) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t226 : ((-85977932323/2500000000000 : ℚ) : ℝ) ≤ stT247o2 226 := by
  have hc : ((-129253/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((226 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85977932323/2500000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-129253/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c227 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((108499/40000 : ℚ) : ℝ) ≤ Real.log ((227 : ℕ)) / 2 := by
    have h := (log_br_227).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((227 : ℕ)) / 2 ≤ ((54249501/20000000 : ℚ) : ℝ) := by
    have h := (log_br_227).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -39221/100000) (δ := 21/2000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t227 : ((632528019/5000000000000 : ℚ) : ℝ) ≤ stT247o2 227 := by
  have hc : ((953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((227 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((632528019/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c228 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((518259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3393341/1250000 : ℚ) : ℝ) ≤ Real.log ((228 : ℕ)) / 2 := by
    have h := (log_br_228).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((228 : ℕ)) / 2 ≤ ((54293457/20000000 : ℚ) : ℝ) := by
    have h := (log_br_228).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -512991/2000000) (δ := 91/10000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t228 : ((171596100797/5000000000000 : ℚ) : ℝ) ≤ stT247o2 228 := by
  have hc : ((518209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((228 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171596100797/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((518209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c229 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((442221/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((2716861/1000000 : ℚ) : ℝ) ≤ Real.log ((229 : ℕ)) / 2 := by
    have h := (log_br_229).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((229 : ℕ)) / 2 ≤ ((54337221/20000000 : ℚ) : ℝ) := by
    have h := (log_br_229).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1213749/10000000) (δ := 121/10000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t229 : ((36526384541/625000000000 : ℚ) : ℝ) ≤ stT247o2 229 := by
  have hc : ((110549/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((229 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36526384541/625000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((110549/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c230 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((199723/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54380793/20000000 : ℚ) : ℝ) ≤ Real.log ((230 : ℕ)) / 2 := by
    have h := (log_br_230).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((230 : ℕ)) / 2 ≤ ((27190397/10000000 : ℚ) : ℝ) := by
    have h := (log_br_230).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 131569/10000000) (δ := 229/20000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t230 : ((6584337897/100000000000 : ℚ) : ℝ) ≤ stT247o2 230 := by
  have hc : ((199713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((230 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6584337897/100000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((199713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c231 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((831819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54424177/20000000 : ℚ) : ℝ) ≤ Real.log ((231 : ℕ)) / 2 := by
    have h := (log_br_231).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((231 : ℕ)) / 2 ≤ ((27212089/10000000 : ℚ) : ℝ) := by
    have h := (log_br_231).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 29421/200000) (δ := 229/20000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t231 : ((547263245319/10000000000000 : ℚ) : ℝ) ≤ stT247o2 231 := by
  have hc : ((831769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((231 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((547263245319/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((831769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c232 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((433973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54467373/20000000 : ℚ) : ℝ) ≤ Real.log ((232 : ℕ)) / 2 := by
    have h := (log_br_232).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((232 : ℕ)) / 2 ≤ ((27233687/10000000 : ℚ) : ℝ) := by
    have h := (log_br_232).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1402373/5000000) (δ := 873/100000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t232 : ((71221083759/2500000000000 : ℚ) : ℝ) ≤ stT247o2 232 := by
  have hc : ((433923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((232 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71221083759/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((433923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c233 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-82193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((3406899/1250000 : ℚ) : ℝ) ≤ Real.log ((233 : ℕ)) / 2 := by
    have h := (log_br_233).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((233 : ℕ)) / 2 ≤ ((10902077/4000000 : ℚ) : ℝ) := by
    have h := (log_br_233).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 826541/2000000) (δ := 81/12500000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t233 : ((-26939599323/5000000000000 : ℚ) : ℝ) ≤ stT247o2 233 := by
  have hc : ((-82243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((233 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26939599323/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-82243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c234 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-286923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54553211/20000000 : ℚ) : ℝ) ≤ Real.log ((234 : ℕ)) / 2 := by
    have h := (log_br_234).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((234 : ℕ)) / 2 ≤ ((13638303/5000000 : ℚ) : ℝ) := by
    have h := (log_br_234).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5454977/10000000) (δ := 211/20000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t234 : ((-46895983377/1250000000000 : ℚ) : ℝ) ≤ stT247o2 234 := by
  have hc : ((-71737/125000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((234 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46895983377/1250000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-71737/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c235 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-907733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10919171/4000000 : ℚ) : ℝ) ≤ Real.log ((235 : ℕ)) / 2 := by
    have h := (log_br_235).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((235 : ℕ)) / 2 ≤ ((3412241/1250000 : ℚ) : ℝ) := by
    have h := (log_br_235).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 677161/1000000) (δ := 43/4000000) (ψ := -750661/1000000) 247 107
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t235 : ((-592173176607/10000000000000 : ℚ) : ℝ) ≤ stT247o2 235 := by
  have hc : ((-907783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((235 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-592173176607/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-907783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c236 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-49791/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27319159/10000000 : ℚ) : ℝ) ≤ Real.log ((236 : ℕ)) / 2 := by
    have h := (log_br_236).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((236 : ℕ)) / 2 ≤ ((54638319/20000000 : ℚ) : ℝ) := by
    have h := (log_br_236).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -7625311/10000000) (δ := 1189/100000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t236 : ((-12965131943/200000000000 : ℚ) : ℝ) ≤ stT247o2 236 := by
  have hc : ((-99587/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((236 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12965131943/200000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-99587/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c237 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-817541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54680601/20000000 : ℚ) : ℝ) ≤ Real.log ((237 : ℕ)) / 2 := by
    have h := (log_br_237).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((237 : ℕ)) / 2 ≤ ((27340301/10000000 : ℚ) : ℝ) := by
    have h := (log_br_237).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -1579953/2500000) (δ := 367/50000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t237 : ((-53108258587/1000000000000 : ℚ) : ℝ) ≤ stT247o2 237 := by
  have hc : ((-817591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((237 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53108258587/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-817591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c238 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-423339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27361353/10000000 : ℚ) : ℝ) ≤ Real.log ((238 : ℕ)) / 2 := by
    have h := (log_br_238).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((238 : ℕ)) / 2 ≤ ((54722707/20000000 : ℚ) : ℝ) := by
    have h := (log_br_238).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -501981/1000000) (δ := 909/100000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t238 : ((-68610610839/2500000000000 : ℚ) : ℝ) ≤ stT247o2 238 := by
  have hc : ((-423389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((238 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68610610839/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-423389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c239 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((16121/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((10952927/4000000 : ℚ) : ℝ) ≤ Real.log ((239 : ℕ)) / 2 := by
    have h := (log_br_239).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((239 : ℕ)) / 2 ≤ ((13691159/5000000 : ℚ) : ℝ) := by
    have h := (log_br_239).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3725259/10000000) (δ := 317/50000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t239 : ((5210667953/1000000000000 : ℚ) : ℝ) ≤ stT247o2 239 := by
  have hc : ((16111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((239 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5210667953/1000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((16111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c240 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((561627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54806389/20000000 : ℚ) : ℝ) ≤ Real.log ((240 : ℕ)) / 2 := by
    have h := (log_br_240).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((240 : ℕ)) / 2 ≤ ((5480639/2000000 : ℚ) : ℝ) := by
    have h := (log_br_240).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2436113/10000000) (δ := 477/50000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t240 : ((362496268769/10000000000000 : ℚ) : ℝ) ≤ stT247o2 240 := by
  have hc : ((561577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((240 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362496268769/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((561577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c241 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((895639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54847969/20000000 : ℚ) : ℝ) ≤ Real.log ((241 : ℕ)) / 2 := by
    have h := (log_br_241).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((241 : ℕ)) / 2 ≤ ((5484797/2000000 : ℚ) : ℝ) := by
    have h := (log_br_241).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -144041/1250000) (δ := 427/50000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t241 : ((144224756971/2500000000000 : ℚ) : ℝ) ≤ stT247o2 241 := by
  have hc : ((895589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((241 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144224756971/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((895589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c242 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((998727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((54889377/20000000 : ℚ) : ℝ) ≤ Real.log ((242 : ℕ)) / 2 := by
    have h := (log_br_242).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((242 : ℕ)) / 2 ≤ ((27444689/10000000 : ℚ) : ℝ) := by
    have h := (log_br_242).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 63071/5000000) (δ := 467/50000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t242 : ((80246692981/1250000000000 : ℚ) : ℝ) ≤ stT247o2 242 := by
  have hc : ((998677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((242 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80246692981/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((998677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c243 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((169479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27465307/10000000 : ℚ) : ℝ) ≤ Real.log ((243 : ℕ)) / 2 := by
    have h := (log_br_243).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((243 : ℕ)) / 2 ≤ ((10986123/4000000 : ℚ) : ℝ) := by
    have h := (log_br_243).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 69967/500000) (δ := 709/100000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t243 : ((217428727/4000000000 : ℚ) : ℝ) ≤ stT247o2 243 := by
  have hc : ((169469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((243 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217428727/4000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((169469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c244 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((482821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((27485841/10000000 : ℚ) : ℝ) ≤ Real.log ((244 : ℕ)) / 2 := by
    have h := (log_br_244).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((244 : ℕ)) / 2 ≤ ((54971683/20000000 : ℚ) : ℝ) := by
    have h := (log_br_244).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 2667309/10000000) (δ := 929/100000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t244 : ((38632783733/1250000000000 : ℚ) : ℝ) ≤ stT247o2 244 := by
  have hc : ((482771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((244 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38632783733/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((482771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c245 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-31/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55012581/20000000 : ℚ) : ℝ) ≤ Real.log ((245 : ℕ)) / 2 := by
    have h := (log_br_245).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((245 : ℕ)) / 2 ≤ ((55012583/20000000 : ℚ) : ℝ) := by
    have h := (log_br_245).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 982523/2500000) (δ := 341/25000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t245 : ((-82415133/1000000000000 : ℚ) : ℝ) ≤ stT247o2 245 := by
  have hc : ((-129/100000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((245 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82415133/1000000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-129/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c246 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-483191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((11010663/4000000 : ℚ) : ℝ) ≤ Real.log ((246 : ℕ)) / 2 := by
    have h := (log_br_246).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((246 : ℕ)) / 2 ≤ ((13763329/5000000 : ℚ) : ℝ) := by
    have h := (log_br_246).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 5187731/10000000) (δ := 201/25000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t246 : ((-308103347057/10000000000000 : ℚ) : ℝ) ≤ stT247o2 246 := by
  have hc : ((-483241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((246 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308103347057/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-483241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c247 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-844329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55093883/20000000 : ℚ) : ℝ) ≤ Real.log ((247 : ℕ)) / 2 := by
    have h := (log_br_247).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((247 : ℕ)) / 2 ≤ ((13773471/5000000 : ℚ) : ℝ) := by
    have h := (log_br_247).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 1610067/2500000) (δ := 201/25000000) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t247 : ((-107453138403/2000000000000 : ℚ) : ℝ) ≤ stT247o2 247 := by
  have hc : ((-844379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((247 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107453138403/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-844379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c248 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-99779/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55134287/20000000 : ℚ) : ℝ) ≤ Real.log ((248 : ℕ)) / 2 := by
    have h := (log_br_248).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((248 : ℕ)) / 2 ≤ ((3445893/1250000 : ℚ) : ℝ) := by
    have h := (log_br_248).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := 120121/156250) (δ := 11/1562500) (ψ := -750661/1000000) 247 108
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t248 : ((-7920367473/125000000000 : ℚ) : ℝ) ≤ stT247o2 248 := by
  have hc : ((-12473/12500 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((248 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7920367473/125000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-12473/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c249 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-454381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((431051/156250 : ℚ) : ℝ) ≤ Real.log ((249 : ℕ)) / 2 := by
    have h := (log_br_249).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((249 : ℕ)) / 2 ≤ ((55174529/20000000 : ℚ) : ℝ) := by
    have h := (log_br_249).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -3388881/5000000) (δ := 119/10000000) (ψ := -750661/1000000) 247 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t249 : ((-5759368847/100000000000 : ℚ) : ℝ) ≤ stT247o2 249 := by
  have hc : ((-227203/250000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((249 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5759368847/100000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-227203/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_c250 :
    |Real.cos (((247 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-601453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact cosMulShift_eval (r := -2770143/5000000) (δ := 1043/100000000) (ψ := -750661/1000000) 247 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st247o2_t250 : ((-47553022671/1250000000000 : ℚ) : ℝ) ≤ stT247o2 250 := by
  have hc : ((-601503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((247 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st247o2_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47553022671/1250000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-601503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st247o2_p1 : ((182797/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT247o2 (i+1) := by
  rw [Finset.sum_range_one]
  exact st247o2_t1

theorem st247o2_p2 : ((3516286407/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 1, stT247o2 (i+1)) + stT247o2 2 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 1
    simpa using h
  have hprev := st247o2_p1
  have hstep := st247o2_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p3 : ((571604092491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 2, stT247o2 (i+1)) + stT247o2 3 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 2
    simpa using h
  have hprev := st247o2_p2
  have hstep := st247o2_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p4 : ((93594609987/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 3, stT247o2 (i+1)) + stT247o2 4 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 3
    simpa using h
  have hprev := st247o2_p3
  have hstep := st247o2_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p5 : ((245192353637/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 4, stT247o2 (i+1)) + stT247o2 5 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 4
    simpa using h
  have hprev := st247o2_p4
  have hstep := st247o2_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p6 : ((315515275157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 5, stT247o2 (i+1)) + stT247o2 6 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 5
    simpa using h
  have hprev := st247o2_p5
  have hstep := st247o2_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p7 : ((-557421582227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 6, stT247o2 (i+1)) + stT247o2 7 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 6
    simpa using h
  have hprev := st247o2_p6
  have hstep := st247o2_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p8 : ((650720698487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 7, stT247o2 (i+1)) + stT247o2 8 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 7
    simpa using h
  have hprev := st247o2_p7
  have hstep := st247o2_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p9 : ((31654457169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 8, stT247o2 (i+1)) + stT247o2 9 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 8
    simpa using h
  have hprev := st247o2_p8
  have hstep := st247o2_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p10 : ((-538681353799/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 9, stT247o2 (i+1)) + stT247o2 10 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 9
    simpa using h
  have hprev := st247o2_p9
  have hstep := st247o2_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p11 : ((-218569365109/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 10, stT247o2 (i+1)) + stT247o2 11 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 10
    simpa using h
  have hprev := st247o2_p10
  have hstep := st247o2_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p12 : ((618551118579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 11, stT247o2 (i+1)) + stT247o2 12 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 11
    simpa using h
  have hprev := st247o2_p11
  have hstep := st247o2_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p13 : ((-2087603730139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 12, stT247o2 (i+1)) + stT247o2 13 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 12
    simpa using h
  have hprev := st247o2_p12
  have hstep := st247o2_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p14 : ((581346791421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 13, stT247o2 (i+1)) + stT247o2 14 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 13
    simpa using h
  have hprev := st247o2_p13
  have hstep := st247o2_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p15 : ((-454497666651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 14, stT247o2 (i+1)) + stT247o2 15 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 14
    simpa using h
  have hprev := st247o2_p14
  have hstep := st247o2_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p16 : ((-1384553038673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 15, stT247o2 (i+1)) + stT247o2 16 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 15
    simpa using h
  have hprev := st247o2_p15
  have hstep := st247o2_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p17 : ((-951830722577/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 16, stT247o2 (i+1)) + stT247o2 17 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 16
    simpa using h
  have hprev := st247o2_p16
  have hstep := st247o2_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p18 : ((119341495543/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 17, stT247o2 (i+1)) + stT247o2 18 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 17
    simpa using h
  have hprev := st247o2_p17
  have hstep := st247o2_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p19 : ((506250028057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 18, stT247o2 (i+1)) + stT247o2 19 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 18
    simpa using h
  have hprev := st247o2_p18
  have hstep := st247o2_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p20 : ((2383465150347/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 19, stT247o2 (i+1)) + stT247o2 20 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 19
    simpa using h
  have hprev := st247o2_p19
  have hstep := st247o2_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p21 : ((3442722719861/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 20, stT247o2 (i+1)) + stT247o2 21 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 20
    simpa using h
  have hprev := st247o2_p20
  have hstep := st247o2_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p22 : ((420058085213/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 21, stT247o2 (i+1)) + stT247o2 22 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 21
    simpa using h
  have hprev := st247o2_p21
  have hstep := st247o2_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p23 : ((839585292509/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 22, stT247o2 (i+1)) + stT247o2 23 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 22
    simpa using h
  have hprev := st247o2_p22
  have hstep := st247o2_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p24 : ((1661562323339/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 23, stT247o2 (i+1)) + stT247o2 24 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 23
    simpa using h
  have hprev := st247o2_p23
  have hstep := st247o2_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p25 : ((5117034528749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 24, stT247o2 (i+1)) + stT247o2 25 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 24
    simpa using h
  have hprev := st247o2_p24
  have hstep := st247o2_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p26 : ((617371003671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 25, stT247o2 (i+1)) + stT247o2 26 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 25
    simpa using h
  have hprev := st247o2_p25
  have hstep := st247o2_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p27 : ((773932927671/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 26, stT247o2 (i+1)) + stT247o2 27 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 26
    simpa using h
  have hprev := st247o2_p26
  have hstep := st247o2_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p28 : ((3165040353159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 27, stT247o2 (i+1)) + stT247o2 28 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 27
    simpa using h
  have hprev := st247o2_p27
  have hstep := st247o2_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p29 : ((2846037939407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 28, stT247o2 (i+1)) + stT247o2 29 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 28
    simpa using h
  have hprev := st247o2_p28
  have hstep := st247o2_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p30 : ((468117461877/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 29, stT247o2 (i+1)) + stT247o2 30 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 29
    simpa using h
  have hprev := st247o2_p29
  have hstep := st247o2_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p31 : ((769387793343/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 30, stT247o2 (i+1)) + stT247o2 31 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 30
    simpa using h
  have hprev := st247o2_p30
  have hstep := st247o2_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p32 : ((3129054151899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 31, stT247o2 (i+1)) + stT247o2 32 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 31
    simpa using h
  have hprev := st247o2_p31
  have hstep := st247o2_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p33 : ((3620723277279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 32, stT247o2 (i+1)) + stT247o2 33 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 32
    simpa using h
  have hprev := st247o2_p32
  have hstep := st247o2_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p34 : ((1419769718421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 33, stT247o2 (i+1)) + stT247o2 34 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 33
    simpa using h
  have hprev := st247o2_p33
  have hstep := st247o2_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p35 : ((460572206343/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 34, stT247o2 (i+1)) + stT247o2 35 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 34
    simpa using h
  have hprev := st247o2_p34
  have hstep := st247o2_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p36 : ((5803843321759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 35, stT247o2 (i+1)) + stT247o2 36 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 35
    simpa using h
  have hprev := st247o2_p35
  have hstep := st247o2_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p37 : ((447949493221/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 36, stT247o2 (i+1)) + stT247o2 37 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 36
    simpa using h
  have hprev := st247o2_p36
  have hstep := st247o2_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p38 : ((746802828007/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 37, stT247o2 (i+1)) + stT247o2 38 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 37
    simpa using h
  have hprev := st247o2_p37
  have hstep := st247o2_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p39 : ((884631488801/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 38, stT247o2 (i+1)) + stT247o2 39 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 38
    simpa using h
  have hprev := st247o2_p38
  have hstep := st247o2_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p40 : ((5971236497727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 39, stT247o2 (i+1)) + stT247o2 40 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 39
    simpa using h
  have hprev := st247o2_p39
  have hstep := st247o2_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p41 : ((7161320696889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 40, stT247o2 (i+1)) + stT247o2 41 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 40
    simpa using h
  have hprev := st247o2_p40
  have hstep := st247o2_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p42 : ((5836769510051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 41, stT247o2 (i+1)) + stT247o2 42 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 41
    simpa using h
  have hprev := st247o2_p41
  have hstep := st247o2_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p43 : ((3646067184923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 42, stT247o2 (i+1)) + stT247o2 43 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 42
    simpa using h
  have hprev := st247o2_p42
  have hstep := st247o2_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p44 : ((1446125497999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 43, stT247o2 (i+1)) + stT247o2 44 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 43
    simpa using h
  have hprev := st247o2_p43
  have hstep := st247o2_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p45 : ((179417819299/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 44, stT247o2 (i+1)) + stT247o2 45 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 44
    simpa using h
  have hprev := st247o2_p44
  have hstep := st247o2_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p46 : ((76770247521/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 45, stT247o2 (i+1)) + stT247o2 46 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 45
    simpa using h
  have hprev := st247o2_p45
  have hstep := st247o2_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p47 : ((1312457376007/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 46, stT247o2 (i+1)) + stT247o2 47 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 46
    simpa using h
  have hprev := st247o2_p46
  have hstep := st247o2_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p48 : ((1383552832357/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 47, stT247o2 (i+1)) + stT247o2 48 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 47
    simpa using h
  have hprev := st247o2_p47
  have hstep := st247o2_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p49 : ((1170021318373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 48, stT247o2 (i+1)) + stT247o2 49 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 48
    simpa using h
  have hprev := st247o2_p48
  have hstep := st247o2_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p50 : ((3629849678997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 49, stT247o2 (i+1)) + stT247o2 50 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 49
    simpa using h
  have hprev := st247o2_p49
  have hstep := st247o2_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p51 : ((48932090799/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 50, stT247o2 (i+1)) + stT247o2 51 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 50
    simpa using h
  have hprev := st247o2_p50
  have hstep := st247o2_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p52 : ((51261575637/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 51, stT247o2 (i+1)) + stT247o2 52 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 51
    simpa using h
  have hprev := st247o2_p51
  have hstep := st247o2_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p53 : ((715756578099/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 52, stT247o2 (i+1)) + stT247o2 53 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 52
    simpa using h
  have hprev := st247o2_p52
  have hstep := st247o2_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p54 : ((2907041447339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 53, stT247o2 (i+1)) + stT247o2 54 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 53
    simpa using h
  have hprev := st247o2_p53
  have hstep := st247o2_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p55 : ((6831890866651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 54, stT247o2 (i+1)) + stT247o2 55 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 54
    simpa using h
  have hprev := st247o2_p54
  have hstep := st247o2_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p56 : ((55304614411/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 55, stT247o2 (i+1)) + stT247o2 56 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 55
    simpa using h
  have hprev := st247o2_p55
  have hstep := st247o2_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p57 : ((1157354682031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 56, stT247o2 (i+1)) + stT247o2 57 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 56
    simpa using h
  have hprev := st247o2_p56
  have hstep := st247o2_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p58 : ((1395002196199/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 57, stT247o2 (i+1)) + stT247o2 58 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 57
    simpa using h
  have hprev := st247o2_p57
  have hstep := st247o2_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p59 : ((273751583289/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 58, stT247o2 (i+1)) + stT247o2 59 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 58
    simpa using h
  have hprev := st247o2_p58
  have hstep := st247o2_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p60 : ((144561597093/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 59, stT247o2 (i+1)) + stT247o2 60 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 59
    simpa using h
  have hprev := st247o2_p59
  have hstep := st247o2_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p61 : ((863679034251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 60, stT247o2 (i+1)) + stT247o2 61 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 60
    simpa using h
  have hprev := st247o2_p60
  have hstep := st247o2_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p62 : ((218180677843/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 61, stT247o2 (i+1)) + stT247o2 62 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 61
    simpa using h
  have hprev := st247o2_p61
  have hstep := st247o2_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p63 : ((2898721737789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 62, stT247o2 (i+1)) + stT247o2 63 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 62
    simpa using h
  have hprev := st247o2_p62
  have hstep := st247o2_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p64 : ((3311896112789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 63, stT247o2 (i+1)) + stT247o2 64 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 63
    simpa using h
  have hprev := st247o2_p63
  have hstep := st247o2_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p65 : ((902909902289/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 64, stT247o2 (i+1)) + stT247o2 65 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 64
    simpa using h
  have hprev := st247o2_p64
  have hstep := st247o2_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p66 : ((3007200029321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 65, stT247o2 (i+1)) + stT247o2 66 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 65
    simpa using h
  have hprev := st247o2_p65
  have hstep := st247o2_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p67 : ((1533047421413/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 66, stT247o2 (i+1)) + stT247o2 67 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 66
    simpa using h
  have hprev := st247o2_p66
  have hstep := st247o2_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p68 : ((3634494605257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 67, stT247o2 (i+1)) + stT247o2 68 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 67
    simpa using h
  have hprev := st247o2_p67
  have hstep := st247o2_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p69 : ((33007572017/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 68, stT247o2 (i+1)) + stT247o2 69 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 68
    simpa using h
  have hprev := st247o2_p68
  have hstep := st247o2_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p70 : ((1152694722781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 69, stT247o2 (i+1)) + stT247o2 70 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 69
    simpa using h
  have hprev := st247o2_p69
  have hstep := st247o2_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p71 : ((843202394107/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 70, stT247o2 (i+1)) + stT247o2 71 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 70
    simpa using h
  have hprev := st247o2_p70
  have hstep := st247o2_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p72 : ((289877319341/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 71, stT247o2 (i+1)) + stT247o2 72 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 71
    simpa using h
  have hprev := st247o2_p71
  have hstep := st247o2_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p73 : ((6131099635909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 72, stT247o2 (i+1)) + stT247o2 73 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 72
    simpa using h
  have hprev := st247o2_p72
  have hstep := st247o2_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p74 : ((5903221594553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 73, stT247o2 (i+1)) + stT247o2 74 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 73
    simpa using h
  have hprev := st247o2_p73
  have hstep := st247o2_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p75 : ((7050845592953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 74, stT247o2 (i+1)) + stT247o2 75 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 74
    simpa using h
  have hprev := st247o2_p74
  have hstep := st247o2_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p76 : ((1420551092153/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 75, stT247o2 (i+1)) + stT247o2 76 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 75
    simpa using h
  have hprev := st247o2_p75
  have hstep := st247o2_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p77 : ((5963093620071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 76, stT247o2 (i+1)) + stT247o2 77 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 76
    simpa using h
  have hprev := st247o2_p76
  have hstep := st247o2_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p78 : ((1496720406891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 77, stT247o2 (i+1)) + stT247o2 78 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 77
    simpa using h
  have hprev := st247o2_p77
  have hstep := st247o2_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p79 : ((1422320144823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 78, stT247o2 (i+1)) + stT247o2 79 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 78
    simpa using h
  have hprev := st247o2_p78
  have hstep := st247o2_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p80 : ((7104594005037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 79, stT247o2 (i+1)) + stT247o2 80 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 79
    simpa using h
  have hprev := st247o2_p79
  have hstep := st247o2_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p81 : ((5993939783181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 80, stT247o2 (i+1)) + stT247o2 81 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 80
    simpa using h
  have hprev := st247o2_p80
  have hstep := st247o2_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p82 : ((5899209348069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 81, stT247o2 (i+1)) + stT247o2 82 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 81
    simpa using h
  have hprev := st247o2_p81
  have hstep := st247o2_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p83 : ((6982838850297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 82, stT247o2 (i+1)) + stT247o2 83 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 82
    simpa using h
  have hprev := st247o2_p82
  have hstep := st247o2_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p84 : ((3627092523487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 83, stT247o2 (i+1)) + stT247o2 84 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 83
    simpa using h
  have hprev := st247o2_p83
  have hstep := st247o2_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p85 : ((6239245949243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 84, stT247o2 (i+1)) + stT247o2 85 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 84
    simpa using h
  have hprev := st247o2_p84
  have hstep := st247o2_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p86 : ((5734599228523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 85, stT247o2 (i+1)) + stT247o2 86 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 85
    simpa using h
  have hprev := st247o2_p85
  have hstep := st247o2_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p87 : ((1320169070879/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 86, stT247o2 (i+1)) + stT247o2 87 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 86
    simpa using h
  have hprev := st247o2_p86
  have hstep := st247o2_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p88 : ((1839385030481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 87, stT247o2 (i+1)) + stT247o2 88 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 87
    simpa using h
  have hprev := st247o2_p87
  have hstep := st247o2_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p89 : ((3376799420719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 88, stT247o2 (i+1)) + stT247o2 89 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 88
    simpa using h
  have hprev := st247o2_p88
  have hstep := st247o2_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p90 : ((5789037338579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 89, stT247o2 (i+1)) + stT247o2 90 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 89
    simpa using h
  have hprev := st247o2_p89
  have hstep := st247o2_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p91 : ((6006601344791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 90, stT247o2 (i+1)) + stT247o2 91 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 90
    simpa using h
  have hprev := st247o2_p90
  have hstep := st247o2_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p92 : ((7049047193579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 91, stT247o2 (i+1)) + stT247o2 92 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 91
    simpa using h
  have hprev := st247o2_p91
  have hstep := st247o2_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p93 : ((7303118853697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 92, stT247o2 (i+1)) + stT247o2 93 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 92
    simpa using h
  have hprev := st247o2_p92
  have hstep := st247o2_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p94 : ((6396685603079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 93, stT247o2 (i+1)) + stT247o2 94 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 93
    simpa using h
  have hprev := st247o2_p93
  have hstep := st247o2_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p95 : ((2844378507571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 94, stT247o2 (i+1)) + stT247o2 95 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 94
    simpa using h
  have hprev := st247o2_p94
  have hstep := st247o2_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p96 : ((3103115373461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 95, stT247o2 (i+1)) + stT247o2 96 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 95
    simpa using h
  have hprev := st247o2_p95
  have hstep := st247o2_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p97 : ((3596116623761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 96, stT247o2 (i+1)) + stT247o2 97 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 96
    simpa using h
  have hprev := st247o2_p96
  have hstep := st247o2_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p98 : ((3628056114773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 97, stT247o2 (i+1)) + stT247o2 98 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 97
    simpa using h
  have hprev := st247o2_p97
  have hstep := st247o2_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p99 : ((3161416971373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 98, stT247o2 (i+1)) + stT247o2 99 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 98
    simpa using h
  have hprev := st247o2_p98
  have hstep := st247o2_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p100 : ((2835517471373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 99, stT247o2 (i+1)) + stT247o2 100 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 99
    simpa using h
  have hprev := st247o2_p99
  have hstep := st247o2_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p101 : ((6164516577637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 100, stT247o2 (i+1)) + stT247o2 101 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 100
    simpa using h
  have hprev := st247o2_p100
  have hstep := st247o2_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p102 : ((7141175795203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 101, stT247o2 (i+1)) + stT247o2 102 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 101
    simpa using h
  have hprev := st247o2_p101
  have hstep := st247o2_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p103 : ((293512637323/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 102, stT247o2 (i+1)) + stT247o2 103 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 102
    simpa using h
  have hprev := st247o2_p102
  have hstep := st247o2_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p104 : ((6516751927831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 103, stT247o2 (i+1)) + stT247o2 104 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 103
    simpa using h
  have hprev := st247o2_p103
  have hstep := st247o2_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p105 : ((2856542383809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 104, stT247o2 (i+1)) + stT247o2 105 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 104
    simpa using h
  have hprev := st247o2_p104
  have hstep := st247o2_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p106 : ((5908986153123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 105, stT247o2 (i+1)) + stT247o2 106 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 105
    simpa using h
  have hprev := st247o2_p105
  have hstep := st247o2_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p107 : ((6854830988163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 106, stT247o2 (i+1)) + stT247o2 107 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 106
    simpa using h
  have hprev := st247o2_p106
  have hstep := st247o2_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p108 : ((7421669369163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 107, stT247o2 (i+1)) + stT247o2 108 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 107
    simpa using h
  have hprev := st247o2_p107
  have hstep := st247o2_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p109 : ((1738867755647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 108, stT247o2 (i+1)) + stT247o2 109 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 108
    simpa using h
  have hprev := st247o2_p108
  have hstep := st247o2_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p110 : ((150099875987/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 109, stT247o2 (i+1)) + stT247o2 110 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 109
    simpa using h
  have hprev := st247o2_p109
  have hstep := st247o2_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p111 : ((2822512216519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 110, stT247o2 (i+1)) + stT247o2 111 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 110
    simpa using h
  have hprev := st247o2_p110
  have hstep := st247o2_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p112 : ((1566979803337/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 111, stT247o2 (i+1)) + stT247o2 112 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 111
    simpa using h
  have hprev := st247o2_p111
  have hstep := st247o2_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p113 : ((1795020679257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 112, stT247o2 (i+1)) + stT247o2 113 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 112
    simpa using h
  have hprev := st247o2_p112
  have hstep := st247o2_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p114 : ((3699448535289/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 113, stT247o2 (i+1)) + stT247o2 114 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 113
    simpa using h
  have hprev := st247o2_p113
  have hstep := st247o2_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p115 : ((6702758775453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 114, stT247o2 (i+1)) + stT247o2 115 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 114
    simpa using h
  have hprev := st247o2_p114
  have hstep := st247o2_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p116 : ((5827765764561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 115, stT247o2 (i+1)) + stT247o2 116 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 115
    simpa using h
  have hprev := st247o2_p115
  have hstep := st247o2_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p117 : ((283589151567/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 116, stT247o2 (i+1)) + stT247o2 117 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 116
    simpa using h
  have hprev := st247o2_p116
  have hstep := st247o2_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p118 : ((3191095453857/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 117, stT247o2 (i+1)) + stT247o2 118 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 117
    simpa using h
  have hprev := st247o2_p117
  have hstep := st247o2_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p119 : ((724232130753/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 118, stT247o2 (i+1)) + stT247o2 119 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 118
    simpa using h
  have hprev := st247o2_p118
  have hstep := st247o2_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p120 : ((740958830337/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 119, stT247o2 (i+1)) + stT247o2 120 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 119
    simpa using h
  have hprev := st247o2_p119
  have hstep := st247o2_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p121 : ((6732243690181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 120, stT247o2 (i+1)) + stT247o2 121 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 120
    simpa using h
  have hprev := st247o2_p120
  have hstep := st247o2_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p122 : ((5863679439301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 121, stT247o2 (i+1)) + stT247o2 122 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 121
    simpa using h
  have hprev := st247o2_p121
  have hstep := st247o2_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p123 : ((5617592056221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 122, stT247o2 (i+1)) + stT247o2 123 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 122
    simpa using h
  have hprev := st247o2_p122
  have hstep := st247o2_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p124 : ((6212136455703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 123, stT247o2 (i+1)) + stT247o2 124 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 123
    simpa using h
  have hprev := st247o2_p123
  have hstep := st247o2_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p125 : ((7097157661371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 124, stT247o2 (i+1)) + stT247o2 125 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 124
    simpa using h
  have hprev := st247o2_p124
  have hstep := st247o2_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p126 : ((7478120399471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 125, stT247o2 (i+1)) + stT247o2 126 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 125
    simpa using h
  have hprev := st247o2_p125
  have hstep := st247o2_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p127 : ((3513074774153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 126, stT247o2 (i+1)) + stT247o2 127 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 126
    simpa using h
  have hprev := st247o2_p126
  have hstep := st247o2_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p128 : ((3072125817827/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 127, stT247o2 (i+1)) + stT247o2 128 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 127
    simpa using h
  have hprev := st247o2_p127
  have hstep := st247o2_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p129 : ((5592299545107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 128, stT247o2 (i+1)) + stT247o2 129 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 128
    simpa using h
  have hprev := st247o2_p128
  have hstep := st247o2_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p130 : ((5831407482357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 129, stT247o2 (i+1)) + stT247o2 130 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 129
    simpa using h
  have hprev := st247o2_p129
  have hstep := st247o2_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p131 : ((6652617598629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 130, stT247o2 (i+1)) + stT247o2 131 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 130
    simpa using h
  have hprev := st247o2_p130
  have hstep := st247o2_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p132 : ((7375374738009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 131, stT247o2 (i+1)) + stT247o2 132 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 131
    simpa using h
  have hprev := st247o2_p131
  have hstep := st247o2_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p133 : ((46354810341/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 132, stT247o2 (i+1)) + stT247o2 133 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 132
    simpa using h
  have hprev := st247o2_p132
  have hstep := st247o2_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p134 : ((337620128071/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 133, stT247o2 (i+1)) + stT247o2 134 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 133
    simpa using h
  have hprev := st247o2_p133
  have hstep := st247o2_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p135 : ((739166914677/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 134, stT247o2 (i+1)) + stT247o2 135 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 134
    simpa using h
  have hprev := st247o2_p134
  have hstep := st247o2_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p136 : ((5552216717847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 135, stT247o2 (i+1)) + stT247o2 136 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 135
    simpa using h
  have hprev := st247o2_p135
  have hstep := st247o2_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p137 : ((74239960833/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 136, stT247o2 (i+1)) + stT247o2 137 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 136
    simpa using h
  have hprev := st247o2_p136
  have hstep := st247o2_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p138 : ((84662739297/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 137, stT247o2 (i+1)) + stT247o2 138 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 137
    simpa using h
  have hprev := st247o2_p137
  have hstep := st247o2_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p139 : ((928445091779/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 138, stT247o2 (i+1)) + stT247o2 139 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 138
    simpa using h
  have hprev := st247o2_p138
  have hstep := st247o2_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p140 : ((7424366893487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 139, stT247o2 (i+1)) + stT247o2 140 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 139
    simpa using h
  have hprev := st247o2_p139
  have hstep := st247o2_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p141 : ((6773780051079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 140, stT247o2 (i+1)) + stT247o2 141 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 140
    simpa using h
  have hprev := st247o2_p140
  have hstep := st247o2_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p142 : ((5948834773709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 141, stT247o2 (i+1)) + stT247o2 142 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 141
    simpa using h
  have hprev := st247o2_p141
  have hstep := st247o2_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p143 : ((5533722076023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 142, stT247o2 (i+1)) + stT247o2 143 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 142
    simpa using h
  have hprev := st247o2_p142
  have hstep := st247o2_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p144 : ((726569933061/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 143, stT247o2 (i+1)) + stT247o2 144 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 143
    simpa using h
  have hprev := st247o2_p143
  have hstep := st247o2_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p145 : ((3292648870971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 144, stT247o2 (i+1)) + stT247o2 145 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 144
    simpa using h
  have hprev := st247o2_p144
  have hstep := st247o2_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p146 : ((7321648531827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 145, stT247o2 (i+1)) + stT247o2 146 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 145
    simpa using h
  have hprev := st247o2_p145
  have hstep := st247o2_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p147 : ((1505750954157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 146, stT247o2 (i+1)) + stT247o2 147 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 146
    simpa using h
  have hprev := st247o2_p146
  have hstep := st247o2_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p148 : ((88448653043/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 147, stT247o2 (i+1)) + stT247o2 148 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 147
    simpa using h
  have hprev := st247o2_p147
  have hstep := st247o2_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p149 : ((78331649863/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 148, stT247o2 (i+1)) + stT247o2 149 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 148
    simpa using h
  have hprev := st247o2_p148
  have hstep := st247o2_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p150 : ((1406672253493/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 149, stT247o2 (i+1)) + stT247o2 150 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 149
    simpa using h
  have hprev := st247o2_p149
  have hstep := st247o2_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p151 : ((2780876767253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 150, stT247o2 (i+1)) + stT247o2 151 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 150
    simpa using h
  have hprev := st247o2_p150
  have hstep := st247o2_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p152 : ((6105844921213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 151, stT247o2 (i+1)) + stT247o2 152 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 151
    simpa using h
  have hprev := st247o2_p151
  have hstep := st247o2_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p153 : ((6913991326357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 152, stT247o2 (i+1)) + stT247o2 153 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 152
    simpa using h
  have hprev := st247o2_p152
  have hstep := st247o2_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p154 : ((7487408620803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 153, stT247o2 (i+1)) + stT247o2 154 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 153
    simpa using h
  have hprev := st247o2_p153
  have hstep := st247o2_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p155 : ((7481327442183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 154, stT247o2 (i+1)) + stT247o2 155 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 154
    simpa using h
  have hprev := st247o2_p154
  have hstep := st247o2_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p156 : ((431623425623/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 155, stT247o2 (i+1)) + stT247o2 156 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 155
    simpa using h
  have hprev := st247o2_p155
  have hstep := st247o2_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p157 : ((763501139899/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 156, stT247o2 (i+1)) + stT247o2 157 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 156
    simpa using h
  have hprev := st247o2_p156
  have hstep := st247o2_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p158 : ((2778052936147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 157, stT247o2 (i+1)) + stT247o2 158 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 157
    simpa using h
  have hprev := st247o2_p157
  have hstep := st247o2_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p159 : ((5566054697089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 158, stT247o2 (i+1)) + stT247o2 159 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 158
    simpa using h
  have hprev := st247o2_p158
  have hstep := st247o2_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p160 : ((3062933441693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 159, stT247o2 (i+1)) + stT247o2 160 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 159
    simpa using h
  have hprev := st247o2_p159
  have hstep := st247o2_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p161 : ((3456927757223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 160, stT247o2 (i+1)) + stT247o2 161 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 160
    simpa using h
  have hprev := st247o2_p160
  have hstep := st247o2_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p162 : ((3744268380873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 161, stT247o2 (i+1)) + stT247o2 162 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 161
    simpa using h
  have hprev := st247o2_p161
  have hstep := st247o2_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p163 : ((3767934190143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 162, stT247o2 (i+1)) + stT247o2 163 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 162
    simpa using h
  have hprev := st247o2_p162
  have hstep := st247o2_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p164 : ((7035869370027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 163, stT247o2 (i+1)) + stT247o2 164 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 163
    simpa using h
  have hprev := st247o2_p163
  have hstep := st247o2_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p165 : ((25053699027/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 164, stT247o2 (i+1)) + stT247o2 165 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 164
    simpa using h
  have hprev := st247o2_p164
  have hstep := st247o2_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p166 : ((70401973299/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 165, stT247o2 (i+1)) + stT247o2 166 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 165
    simpa using h
  have hprev := st247o2_p165
  have hstep := st247o2_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p167 : ((342019024831/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 166, stT247o2 (i+1)) + stT247o2 167 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 166
    simpa using h
  have hprev := st247o2_p166
  have hstep := st247o2_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p168 : ((1465455498691/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 167, stT247o2 (i+1)) + stT247o2 168 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 167
    simpa using h
  have hprev := st247o2_p167
  have hstep := st247o2_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p169 : ((3297341784797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 168, stT247o2 (i+1)) + stT247o2 169 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 168
    simpa using h
  have hprev := st247o2_p168
  have hstep := st247o2_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p170 : ((3647467753473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 169, stT247o2 (i+1)) + stT247o2 170 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 169
    simpa using h
  have hprev := st247o2_p169
  have hstep := st247o2_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p171 : ((3805591759979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 170, stT247o2 (i+1)) + stT247o2 171 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 170
    simpa using h
  have hprev := st247o2_p170
  have hstep := st247o2_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p172 : ((1847598630473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 171, stT247o2 (i+1)) + stT247o2 172 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 171
    simpa using h
  have hprev := st247o2_p171
  have hstep := st247o2_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p173 : ((3373329802703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 172, stT247o2 (i+1)) + stT247o2 173 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 172
    simpa using h
  have hprev := st247o2_p172
  have hstep := st247o2_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p174 : ((239884508809/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 173, stT247o2 (i+1)) + stT247o2 174 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 173
    simpa using h
  have hprev := st247o2_p173
  have hstep := st247o2_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p175 : ((5502974027789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 174, stT247o2 (i+1)) + stT247o2 175 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 174
    simpa using h
  have hprev := st247o2_p174
  have hstep := st247o2_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p176 : ((549640032113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 175, stT247o2 (i+1)) + stT247o2 176 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 175
    simpa using h
  have hprev := st247o2_p175
  have hstep := st247o2_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p177 : ((59754205587/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 176, stT247o2 (i+1)) + stT247o2 177 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 176
    simpa using h
  have hprev := st247o2_p176
  have hstep := st247o2_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p178 : ((268490629861/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 177, stT247o2 (i+1)) + stT247o2 178 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 177
    simpa using h
  have hprev := st247o2_p177
  have hstep := st247o2_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p179 : ((147306218351/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 178, stT247o2 (i+1)) + stT247o2 179 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 178
    simpa using h
  have hprev := st247o2_p178
  have hstep := st247o2_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p180 : ((381909194617/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 179, stT247o2 (i+1)) + stT247o2 180 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 179
    simpa using h
  have hprev := st247o2_p179
  have hstep := st247o2_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p181 : ((741186097097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 180, stT247o2 (i+1)) + stT247o2 181 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 180
    simpa using h
  have hprev := st247o2_p180
  have hstep := st247o2_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p182 : ((679220562097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 181, stT247o2 (i+1)) + stT247o2 182 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 181
    simpa using h
  have hprev := st247o2_p181
  have hstep := st247o2_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p183 : ((3028164669871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 182, stT247o2 (i+1)) + stT247o2 183 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 182
    simpa using h
  have hprev := st247o2_p182
  have hstep := st247o2_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p184 : ((2763195914461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 183, stT247o2 (i+1)) + stT247o2 184 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 183
    simpa using h
  have hprev := st247o2_p183
  have hstep := st247o2_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p185 : ((1357272266133/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 184, stT247o2 (i+1)) + stT247o2 185 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 184
    simpa using h
  have hprev := st247o2_p184
  have hstep := st247o2_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p186 : ((2900838281951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 185, stT247o2 (i+1)) + stT247o2 186 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 185
    simpa using h
  have hprev := st247o2_p185
  have hstep := st247o2_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p187 : ((3240978483671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 186, stT247o2 (i+1)) + stT247o2 187 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 186
    simpa using h
  have hprev := st247o2_p186
  have hstep := st247o2_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p188 : ((3591100680407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 187, stT247o2 (i+1)) + stT247o2 188 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 187
    simpa using h
  have hprev := st247o2_p187
  have hstep := st247o2_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p189 : ((3806076294263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 188, stT247o2 (i+1)) + stT247o2 189 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 188
    simpa using h
  have hprev := st247o2_p188
  have hstep := st247o2_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p190 : ((3799075441213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 189, stT247o2 (i+1)) + stT247o2 190 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 189
    simpa using h
  have hprev := st247o2_p189
  have hstep := st247o2_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p191 : ((7150177640601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 190, stT247o2 (i+1)) + stT247o2 191 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 190
    simpa using h
  have hprev := st247o2_p190
  have hstep := st247o2_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p192 : ((6452402772481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 191, stT247o2 (i+1)) + stT247o2 192 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 191
    simpa using h
  have hprev := st247o2_p191
  have hstep := st247o2_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p193 : ((231390476617/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 192, stT247o2 (i+1)) + stT247o2 193 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 192
    simpa using h
  have hprev := st247o2_p192
  have hstep := st247o2_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p194 : ((5409866700313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 193, stT247o2 (i+1)) + stT247o2 194 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 193
    simpa using h
  have hprev := st247o2_p193
  have hstep := st247o2_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p195 : ((5471077260577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 194, stT247o2 (i+1)) + stT247o2 195 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 194
    simpa using h
  have hprev := st247o2_p194
  have hstep := st247o2_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p196 : ((2970301609811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 195, stT247o2 (i+1)) + stT247o2 196 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 195
    simpa using h
  have hprev := st247o2_p195
  have hstep := st247o2_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p197 : ((829385864309/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 196, stT247o2 (i+1)) + stT247o2 197 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 196
    simpa using h
  have hprev := st247o2_p196
  have hstep := st247o2_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p198 : ((1822379813791/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 197, stT247o2 (i+1)) + stT247o2 198 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 197
    simpa using h
  have hprev := st247o2_p197
  have hstep := st247o2_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p199 : ((3829477711919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 198, stT247o2 (i+1)) + stT247o2 199 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 198
    simpa using h
  have hprev := st247o2_p198
  have hstep := st247o2_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p200 : ((475556737787/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 199, stT247o2 (i+1)) + stT247o2 200 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 199
    simpa using h
  have hprev := st247o2_p199
  have hstep := st247o2_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p201 : ((895208104287/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 200, stT247o2 (i+1)) + stT247o2 201 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 200
    simpa using h
  have hprev := st247o2_p200
  have hstep := st247o2_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p202 : ((3241868803663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 201, stT247o2 (i+1)) + stT247o2 202 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 201
    simpa using h
  have hprev := st247o2_p201
  have hstep := st247o2_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p203 : ((727715272161/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 202, stT247o2 (i+1)) + stT247o2 203 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 202
    simpa using h
  have hprev := st247o2_p202
  have hstep := st247o2_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p204 : ((2705966925417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 203, stT247o2 (i+1)) + stT247o2 204 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 203
    simpa using h
  have hprev := st247o2_p203
  have hstep := st247o2_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p205 : ((2698523047819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 204, stT247o2 (i+1)) + stT247o2 205 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 204
    simpa using h
  have hprev := st247o2_p204
  have hstep := st247o2_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p206 : ((1155733392999/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 205, stT247o2 (i+1)) + stT247o2 206 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 205
    simpa using h
  have hprev := st247o2_p205
  have hstep := st247o2_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p207 : ((1284137255567/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 206, stT247o2 (i+1)) + stT247o2 207 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 206
    simpa using h
  have hprev := st247o2_p206
  have hstep := st247o2_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p208 : ((1419981344117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 207, stT247o2 (i+1)) + stT247o2 208 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 207
    simpa using h
  have hprev := st247o2_p207
  have hstep := st247o2_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p209 : ((7584523624127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 208, stT247o2 (i+1)) + stT247o2 209 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 208
    simpa using h
  have hprev := st247o2_p208
  have hstep := st247o2_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p210 : ((7712653513197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 209, stT247o2 (i+1)) + stT247o2 210 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 209
    simpa using h
  have hprev := st247o2_p209
  have hstep := st247o2_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p211 : ((7444604044041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 210, stT247o2 (i+1)) + stT247o2 211 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 210
    simpa using h
  have hprev := st247o2_p210
  have hstep := st247o2_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p212 : ((3436363612023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 211, stT247o2 (i+1)) + stT247o2 212 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 211
    simpa using h
  have hprev := st247o2_p211
  have hstep := st247o2_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p213 : ((6187515612809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 212, stT247o2 (i+1)) + stT247o2 213 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 212
    simpa using h
  have hprev := st247o2_p212
  have hstep := st247o2_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p214 : ((224517943667/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 213, stT247o2 (i+1)) + stT247o2 214 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 213
    simpa using h
  have hprev := st247o2_p213
  have hstep := st247o2_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p215 : ((533333677963/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 214, stT247o2 (i+1)) + stT247o2 215 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 214
    simpa using h
  have hprev := st247o2_p214
  have hstep := st247o2_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p216 : ((1358862950461/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 215, stT247o2 (i+1)) + stT247o2 216 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 215
    simpa using h
  have hprev := st247o2_p215
  have hstep := st247o2_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p217 : ((1470904455551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 216, stT247o2 (i+1)) + stT247o2 217 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 216
    simpa using h
  have hprev := st247o2_p216
  have hstep := st247o2_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p218 : ((6534146678279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 217, stT247o2 (i+1)) + stT247o2 218 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 217
    simpa using h
  have hprev := st247o2_p217
  have hstep := st247o2_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p219 : ((3591449736329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 218, stT247o2 (i+1)) + stT247o2 219 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 218
    simpa using h
  have hprev := st247o2_p218
  have hstep := st247o2_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p220 : ((381491906267/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 219, stT247o2 (i+1)) + stT247o2 220 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 219
    simpa using h
  have hprev := st247o2_p219
  have hstep := st247o2_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p221 : ((1935020753023/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 220, stT247o2 (i+1)) + stT247o2 221 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 220
    simpa using h
  have hprev := st247o2_p220
  have hstep := st247o2_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p222 : ((7483097667949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 221, stT247o2 (i+1)) + stT247o2 222 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 221
    simpa using h
  have hprev := st247o2_p221
  have hstep := st247o2_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p223 : ((6939165749999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 222, stT247o2 (i+1)) + stT247o2 223 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 222
    simpa using h
  have hprev := st247o2_p222
  have hstep := st247o2_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p224 : ((250905120581/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 223, stT247o2 (i+1)) + stT247o2 224 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 223
    simpa using h
  have hprev := st247o2_p223
  have hstep := st247o2_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p225 : ((5681210385483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 224, stT247o2 (i+1)) + stT247o2 225 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 224
    simpa using h
  have hprev := st247o2_p224
  have hstep := st247o2_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p226 : ((5337298656191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 225, stT247o2 (i+1)) + stT247o2 226 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 225
    simpa using h
  have hprev := st247o2_p225
  have hstep := st247o2_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p227 : ((5338563712229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 226, stT247o2 (i+1)) + stT247o2 227 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 226
    simpa using h
  have hprev := st247o2_p226
  have hstep := st247o2_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p228 : ((5681755913823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 227, stT247o2 (i+1)) + stT247o2 228 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 227
    simpa using h
  have hprev := st247o2_p227
  have hstep := st247o2_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p229 : ((6266178066479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 228, stT247o2 (i+1)) + stT247o2 229 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 228
    simpa using h
  have hprev := st247o2_p228
  have hstep := st247o2_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p230 : ((6924611856179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 229, stT247o2 (i+1)) + stT247o2 230 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 229
    simpa using h
  have hprev := st247o2_p229
  have hstep := st247o2_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p231 : ((3735937550749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 230, stT247o2 (i+1)) + stT247o2 231 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 230
    simpa using h
  have hprev := st247o2_p230
  have hstep := st247o2_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p232 : ((3878379718267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 231, stT247o2 (i+1)) + stT247o2 232 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 231
    simpa using h
  have hprev := st247o2_p231
  have hstep := st247o2_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p233 : ((120357503717/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 232, stT247o2 (i+1)) + stT247o2 233 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 232
    simpa using h
  have hprev := st247o2_p232
  have hstep := st247o2_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p234 : ((915964046359/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 233, stT247o2 (i+1)) + stT247o2 234 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 233
    simpa using h
  have hprev := st247o2_p233
  have hstep := st247o2_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p235 : ((1347107838853/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 234, stT247o2 (i+1)) + stT247o2 235 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 234
    simpa using h
  have hprev := st247o2_p234
  have hstep := st247o2_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p236 : ((1217456519423/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 235, stT247o2 (i+1)) + stT247o2 236 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 235
    simpa using h
  have hprev := st247o2_p235
  have hstep := st247o2_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p237 : ((1111240002249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 236, stT247o2 (i+1)) + stT247o2 237 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 236
    simpa using h
  have hprev := st247o2_p236
  have hstep := st247o2_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p238 : ((5281757567889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 237, stT247o2 (i+1)) + stT247o2 238 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 237
    simpa using h
  have hprev := st247o2_p237
  have hstep := st247o2_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p239 : ((5333864247419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 238, stT247o2 (i+1)) + stT247o2 239 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 238
    simpa using h
  have hprev := st247o2_p238
  have hstep := st247o2_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p240 : ((1424090129047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 239, stT247o2 (i+1)) + stT247o2 240 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 239
    simpa using h
  have hprev := st247o2_p239
  have hstep := st247o2_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p241 : ((784157443009/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 240, stT247o2 (i+1)) + stT247o2 241 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 240
    simpa using h
  have hprev := st247o2_p240
  have hstep := st247o2_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p242 : ((86440413599/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 241, stT247o2 (i+1)) + stT247o2 242 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 241
    simpa using h
  have hprev := st247o2_p241
  have hstep := st247o2_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p243 : ((372940245271/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 242, stT247o2 (i+1)) + stT247o2 243 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 242
    simpa using h
  have hprev := st247o2_p242
  have hstep := st247o2_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p244 : ((1941966793821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 243, stT247o2 (i+1)) + stT247o2 244 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 243
    simpa using h
  have hprev := st247o2_p243
  have hstep := st247o2_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p245 : ((3883521511977/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 244, stT247o2 (i+1)) + stT247o2 245 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 244
    simpa using h
  have hprev := st247o2_p244
  have hstep := st247o2_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p246 : ((7458939676897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 245, stT247o2 (i+1)) + stT247o2 246 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 245
    simpa using h
  have hprev := st247o2_p245
  have hstep := st247o2_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p247 : ((3460836992441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 246, stT247o2 (i+1)) + stT247o2 247 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 246
    simpa using h
  have hprev := st247o2_p246
  have hstep := st247o2_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p248 : ((3144022293521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 247, stT247o2 (i+1)) + stT247o2 248 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 247
    simpa using h
  have hprev := st247o2_p247
  have hstep := st247o2_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p249 : ((2856053851171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 248, stT247o2 (i+1)) + stT247o2 249 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 248
    simpa using h
  have hprev := st247o2_p248
  have hstep := st247o2_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_p250 : ((2665841760487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT247o2 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT247o2 (i+1))
      = (∑ i ∈ Finset.range 249, stT247o2 (i+1)) + stT247o2 250 := by
    have h := Finset.sum_range_succ (fun i => stT247o2 (i+1)) 249
    simpa using h
  have hprev := st247o2_p249
  have hstep := st247o2_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st247o2_s250 :
    |Real.sin (((247 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))
      - ((-798909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) := by
  have hlo : ((55214609/20000000 : ℚ) : ℝ) ≤ Real.log ((250 : ℕ)) / 2 := by
    have h := (log_br_250).1
    push_cast at h ⊢
    linarith
  have hhi : Real.log ((250 : ℕ)) / 2 ≤ ((5521461/2000000 : ℚ) : ℝ) := by
    have h := (log_br_250).2
    push_cast at h ⊢
    linarith
  exact sinMulShift_eval (r := -2770143/5000000) (δ := 1043/100000000) (ψ := -750661/1000000) 247 109
    hlo hhi (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 247/2`** (evaluated boundary). -/
theorem station_247o2_sign : hardyG (((((247:ℕ)):ℝ)/2)) < 0 := by
  have hcore := phase_station_lower_half_eval 247 250 (by norm_num) (by norm_num)
    ((-750661/1000000 : ℚ) : ℝ)
  have hchain := st247o2_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT247o2 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((247 : ℕ) : ℝ) * (Real.log ((i+1 : ℕ)) / 2)
              - ((-750661/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st247o2_c250
  have hsinb := abs_le.mp st247o2_s250
  have hbdy_lo : ((3129380635977/30505000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((247 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ))) / 2
          - ((((247:ℕ)):ℝ)/2)
            * Real.sin (((247 : ℕ) : ℝ) * (Real.log ((250 : ℕ)) / 2) - ((-750661/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((247:ℕ)):ℝ)/2) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((247:ℝ) * (Real.log (250:ℝ) / 2) - ((-750661/1000000 : ℚ) : ℝ))) / 2
        - ((247:ℝ)/2) * Real.sin ((247:ℝ) * (Real.log (250:ℝ) / 2) - ((-750661/1000000 : ℚ) : ℝ))
        ≥ ((24739947/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((247:ℝ)/2) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((24739947/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((24739947/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((24739947/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((247:ℕ)):ℝ)/2)+1) * (((((247:ℕ)):ℝ)/2)+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((907495223943/2500000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2665841760487/5000000000000 : ℚ) : ℝ) + ((3129380635977/30505000000000 : ℚ) : ℝ)
      - ((907495223943/2500000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-750661/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((((247:ℕ)):ℝ)/2)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-750661/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((((247:ℕ)):ℝ)/2)))).re
      - Real.sin ((-750661/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((((247:ℕ)):ℝ)/2)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((((247:ℕ)):ℝ)/2))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((((247:ℕ)):ℝ)/2))
      = ((((((247:ℕ)):ℝ)/2)) * (Real.log (((((247:ℕ)):ℝ)/2)) - Real.log 2
          - Real.log Real.pi) - (((((247:ℕ)):ℝ)/2))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM : ((48162411/10000000 : ℚ) : ℝ) ≤ Real.log (((((247:ℕ)):ℝ)/2))
      ∧ Real.log (((((247:ℕ)):ℝ)/2)) ≤ ((48162413/10000000 : ℚ) : ℝ) := by
    have hsplit : Real.log (((((247:ℕ)):ℝ)/2))
        = Real.log ((((247:ℕ)):ℝ)) - Real.log 2 :=
      Real.log_div (by norm_num) (by norm_num)
    have hM := log_br_247
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
  have hθwin : |(((-750661/1000000 : ℚ) : ℝ) + ((20:ℤ)) * (2*Real.pi) - Real.pi) - theta (((((247:ℕ)):ℝ)/2))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((((247:ℕ)):ℝ)/2)))
    (φ := ((-750661/1000000 : ℚ) : ℝ) + ((20:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-750661/1000000 : ℚ) : ℝ) + ((20:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-750661/1000000 : ℚ)) : ℝ) - Real.pi) + ((20:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-750661/1000000 : ℚ)) : ℝ) - Real.pi) 20).1,
    (cos_sin_shift ((((-750661/1000000 : ℚ)) : ℝ) - Real.pi) 20).2]
  exact cos_sin_flip ((-750661/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_247o2_sign
end AxiomAudit
